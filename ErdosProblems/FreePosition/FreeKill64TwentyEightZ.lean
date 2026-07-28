import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def twentyEightZFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentyEightZFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentyEightZFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentyEightZFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentyEightZFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentyEightZFastPow a n * twentyEightZFastPow a n * a
        else twentyEightZFastPow a n * twentyEightZFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentyEightZ_2 : Nat.Prime 2 := by norm_num
private theorem prime_twentyEightZ_3 : Nat.Prime 3 := by norm_num
private theorem prime_twentyEightZ_5 : Nat.Prime 5 := by norm_num
private theorem prime_twentyEightZ_7 : Nat.Prime 7 := by norm_num
private theorem prime_twentyEightZ_11 : Nat.Prime 11 := by norm_num
private theorem prime_twentyEightZ_13 : Nat.Prime 13 := by norm_num
private theorem prime_twentyEightZ_17 : Nat.Prime 17 := by norm_num
private theorem prime_twentyEightZ_19 : Nat.Prime 19 := by norm_num
private theorem prime_twentyEightZ_23 : Nat.Prime 23 := by norm_num
private theorem prime_twentyEightZ_29 : Nat.Prime 29 := by norm_num
private theorem prime_twentyEightZ_31 : Nat.Prime 31 := by norm_num
private theorem prime_twentyEightZ_37 : Nat.Prime 37 := by norm_num
private theorem prime_twentyEightZ_41 : Nat.Prime 41 := by norm_num
private theorem prime_twentyEightZ_43 : Nat.Prime 43 := by norm_num
private theorem prime_twentyEightZ_47 : Nat.Prime 47 := by norm_num
private theorem prime_twentyEightZ_53 : Nat.Prime 53 := by norm_num
private theorem prime_twentyEightZ_59 : Nat.Prime 59 := by norm_num
private theorem prime_twentyEightZ_61 : Nat.Prime 61 := by norm_num
private theorem prime_twentyEightZ_67 : Nat.Prime 67 := by norm_num
private theorem prime_twentyEightZ_71 : Nat.Prime 71 := by norm_num
private theorem prime_twentyEightZ_73 : Nat.Prime 73 := by norm_num
private theorem prime_twentyEightZ_79 : Nat.Prime 79 := by norm_num
private theorem prime_twentyEightZ_83 : Nat.Prime 83 := by norm_num
private theorem prime_twentyEightZ_89 : Nat.Prime 89 := by norm_num
private theorem prime_twentyEightZ_97 : Nat.Prime 97 := by norm_num
private theorem prime_twentyEightZ_101 : Nat.Prime 101 := by norm_num
private theorem prime_twentyEightZ_103 : Nat.Prime 103 := by norm_num
private theorem prime_twentyEightZ_107 : Nat.Prime 107 := by norm_num
private theorem prime_twentyEightZ_109 : Nat.Prime 109 := by norm_num
private theorem prime_twentyEightZ_113 : Nat.Prime 113 := by norm_num
private theorem prime_twentyEightZ_127 : Nat.Prime 127 := by norm_num
private theorem prime_twentyEightZ_131 : Nat.Prime 131 := by norm_num
private theorem prime_twentyEightZ_137 : Nat.Prime 137 := by norm_num
private theorem prime_twentyEightZ_139 : Nat.Prime 139 := by norm_num
private theorem prime_twentyEightZ_149 : Nat.Prime 149 := by norm_num
private theorem prime_twentyEightZ_151 : Nat.Prime 151 := by norm_num
private theorem prime_twentyEightZ_157 : Nat.Prime 157 := by norm_num
private theorem prime_twentyEightZ_163 : Nat.Prime 163 := by norm_num
private theorem prime_twentyEightZ_167 : Nat.Prime 167 := by norm_num
private theorem prime_twentyEightZ_173 : Nat.Prime 173 := by norm_num
private theorem prime_twentyEightZ_179 : Nat.Prime 179 := by norm_num
private theorem prime_twentyEightZ_191 : Nat.Prime 191 := by norm_num
private theorem prime_twentyEightZ_193 : Nat.Prime 193 := by norm_num
private theorem prime_twentyEightZ_197 : Nat.Prime 197 := by norm_num
private theorem prime_twentyEightZ_211 : Nat.Prime 211 := by norm_num
private theorem prime_twentyEightZ_223 : Nat.Prime 223 := by norm_num
private theorem prime_twentyEightZ_227 : Nat.Prime 227 := by norm_num
private theorem prime_twentyEightZ_229 : Nat.Prime 229 := by norm_num
private theorem prime_twentyEightZ_233 : Nat.Prime 233 := by norm_num
private theorem prime_twentyEightZ_239 : Nat.Prime 239 := by norm_num
private theorem prime_twentyEightZ_241 : Nat.Prime 241 := by norm_num
private theorem prime_twentyEightZ_251 : Nat.Prime 251 := by norm_num
private theorem prime_twentyEightZ_263 : Nat.Prime 263 := by norm_num
private theorem prime_twentyEightZ_269 : Nat.Prime 269 := by norm_num
private theorem prime_twentyEightZ_271 : Nat.Prime 271 := by norm_num
private theorem prime_twentyEightZ_281 : Nat.Prime 281 := by norm_num
private theorem prime_twentyEightZ_283 : Nat.Prime 283 := by norm_num
private theorem prime_twentyEightZ_293 : Nat.Prime 293 := by norm_num
private theorem prime_twentyEightZ_307 : Nat.Prime 307 := by norm_num
private theorem prime_twentyEightZ_311 : Nat.Prime 311 := by norm_num
private theorem prime_twentyEightZ_317 : Nat.Prime 317 := by norm_num
private theorem prime_twentyEightZ_337 : Nat.Prime 337 := by norm_num
private theorem prime_twentyEightZ_347 : Nat.Prime 347 := by norm_num
private theorem prime_twentyEightZ_359 : Nat.Prime 359 := by norm_num
private theorem prime_twentyEightZ_367 : Nat.Prime 367 := by norm_num
private theorem prime_twentyEightZ_373 : Nat.Prime 373 := by norm_num
private theorem prime_twentyEightZ_379 : Nat.Prime 379 := by norm_num
private theorem prime_twentyEightZ_383 : Nat.Prime 383 := by norm_num
private theorem prime_twentyEightZ_397 : Nat.Prime 397 := by norm_num
private theorem prime_twentyEightZ_401 : Nat.Prime 401 := by norm_num
private theorem prime_twentyEightZ_409 : Nat.Prime 409 := by norm_num
private theorem prime_twentyEightZ_419 : Nat.Prime 419 := by norm_num
private theorem prime_twentyEightZ_421 : Nat.Prime 421 := by norm_num
private theorem prime_twentyEightZ_431 : Nat.Prime 431 := by norm_num
private theorem prime_twentyEightZ_439 : Nat.Prime 439 := by norm_num
private theorem prime_twentyEightZ_467 : Nat.Prime 467 := by norm_num
private theorem prime_twentyEightZ_479 : Nat.Prime 479 := by norm_num
private theorem prime_twentyEightZ_487 : Nat.Prime 487 := by norm_num
private theorem prime_twentyEightZ_491 : Nat.Prime 491 := by norm_num
private theorem prime_twentyEightZ_503 : Nat.Prime 503 := by norm_num
private theorem prime_twentyEightZ_521 : Nat.Prime 521 := by norm_num
private theorem prime_twentyEightZ_571 : Nat.Prime 571 := by norm_num
private theorem prime_twentyEightZ_593 : Nat.Prime 593 := by norm_num
private theorem prime_twentyEightZ_601 : Nat.Prime 601 := by norm_num
private theorem prime_twentyEightZ_613 : Nat.Prime 613 := by norm_num
private theorem prime_twentyEightZ_617 : Nat.Prime 617 := by norm_num
private theorem prime_twentyEightZ_619 : Nat.Prime 619 := by norm_num
private theorem prime_twentyEightZ_641 : Nat.Prime 641 := by norm_num
private theorem prime_twentyEightZ_643 : Nat.Prime 643 := by norm_num
private theorem prime_twentyEightZ_659 : Nat.Prime 659 := by norm_num
private theorem prime_twentyEightZ_661 : Nat.Prime 661 := by norm_num
private theorem prime_twentyEightZ_673 : Nat.Prime 673 := by norm_num
private theorem prime_twentyEightZ_677 : Nat.Prime 677 := by norm_num
private theorem prime_twentyEightZ_701 : Nat.Prime 701 := by norm_num
private theorem prime_twentyEightZ_709 : Nat.Prime 709 := by norm_num
private theorem prime_twentyEightZ_811 : Nat.Prime 811 := by norm_num
private theorem prime_twentyEightZ_853 : Nat.Prime 853 := by norm_num
private theorem prime_twentyEightZ_941 : Nat.Prime 941 := by norm_num
private theorem prime_twentyEightZ_953 : Nat.Prime 953 := by norm_num
private theorem prime_twentyEightZ_971 : Nat.Prime 971 := by norm_num
private theorem prime_twentyEightZ_983 : Nat.Prime 983 := by norm_num
private theorem prime_twentyEightZ_991 : Nat.Prime 991 := by norm_num
private theorem prime_twentyEightZ_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_twentyEightZ_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_twentyEightZ_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_twentyEightZ_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_twentyEightZ_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_twentyEightZ_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_twentyEightZ_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_twentyEightZ_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_twentyEightZ_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_twentyEightZ_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_twentyEightZ_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_twentyEightZ_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_twentyEightZ_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_twentyEightZ_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_twentyEightZ_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_twentyEightZ_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_twentyEightZ_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_twentyEightZ_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_twentyEightZ_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_twentyEightZ_1319 : Nat.Prime 1319 := by norm_num
private theorem prime_twentyEightZ_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_twentyEightZ_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_twentyEightZ_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_twentyEightZ_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_twentyEightZ_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_twentyEightZ_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_twentyEightZ_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_twentyEightZ_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_twentyEightZ_1601 : Nat.Prime 1601 := by norm_num
private theorem prime_twentyEightZ_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_twentyEightZ_1667 : Nat.Prime 1667 := by norm_num
private theorem prime_twentyEightZ_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_twentyEightZ_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_twentyEightZ_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_twentyEightZ_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_twentyEightZ_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_twentyEightZ_2003 : Nat.Prime 2003 := by norm_num
private theorem prime_twentyEightZ_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_twentyEightZ_2089 : Nat.Prime 2089 := by norm_num
private theorem prime_twentyEightZ_2141 : Nat.Prime 2141 := by norm_num
private theorem prime_twentyEightZ_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_twentyEightZ_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_twentyEightZ_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_twentyEightZ_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_twentyEightZ_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_twentyEightZ_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_twentyEightZ_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_twentyEightZ_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_twentyEightZ_2719 : Nat.Prime 2719 := by norm_num
private theorem prime_twentyEightZ_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_twentyEightZ_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_twentyEightZ_2939 : Nat.Prime 2939 := by norm_num
private theorem prime_twentyEightZ_2999 : Nat.Prime 2999 := by norm_num
private theorem prime_twentyEightZ_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_twentyEightZ_3019 : Nat.Prime 3019 := by norm_num
private theorem prime_twentyEightZ_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_twentyEightZ_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_twentyEightZ_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_twentyEightZ_3217 : Nat.Prime 3217 := by norm_num
private theorem prime_twentyEightZ_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_twentyEightZ_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_twentyEightZ_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_twentyEightZ_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_twentyEightZ_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_twentyEightZ_3581 : Nat.Prime 3581 := by norm_num
private theorem prime_twentyEightZ_3637 : Nat.Prime 3637 := by norm_num
private theorem prime_twentyEightZ_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_twentyEightZ_3739 : Nat.Prime 3739 := by norm_num
private theorem prime_twentyEightZ_3779 : Nat.Prime 3779 := by norm_num
private theorem prime_twentyEightZ_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_twentyEightZ_4297 : Nat.Prime 4297 := by norm_num
private theorem prime_twentyEightZ_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_twentyEightZ_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_twentyEightZ_4451 : Nat.Prime 4451 := by norm_num
private theorem prime_twentyEightZ_4519 : Nat.Prime 4519 := by norm_num
private theorem prime_twentyEightZ_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_twentyEightZ_4703 : Nat.Prime 4703 := by norm_num
private theorem prime_twentyEightZ_4789 : Nat.Prime 4789 := by norm_num
private theorem prime_twentyEightZ_4919 : Nat.Prime 4919 := by norm_num
private theorem prime_twentyEightZ_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_twentyEightZ_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_twentyEightZ_5527 : Nat.Prime 5527 := by norm_num
private theorem prime_twentyEightZ_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_twentyEightZ_5581 : Nat.Prime 5581 := by norm_num
private theorem prime_twentyEightZ_5741 : Nat.Prime 5741 := by norm_num
private theorem prime_twentyEightZ_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_twentyEightZ_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_twentyEightZ_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_twentyEightZ_6079 : Nat.Prime 6079 := by norm_num
private theorem prime_twentyEightZ_6229 : Nat.Prime 6229 := by norm_num
private theorem prime_twentyEightZ_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_twentyEightZ_6389 : Nat.Prime 6389 := by norm_num
private theorem prime_twentyEightZ_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_twentyEightZ_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_twentyEightZ_6971 : Nat.Prime 6971 := by norm_num
private theorem prime_twentyEightZ_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_twentyEightZ_7309 : Nat.Prime 7309 := by norm_num
private theorem prime_twentyEightZ_7331 : Nat.Prime 7331 := by norm_num
private theorem prime_twentyEightZ_7681 : Nat.Prime 7681 := by norm_num
private theorem prime_twentyEightZ_7691 : Nat.Prime 7691 := by norm_num
private theorem prime_twentyEightZ_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_twentyEightZ_7823 : Nat.Prime 7823 := by norm_num
private theorem prime_twentyEightZ_7993 : Nat.Prime 7993 := by norm_num
private theorem prime_twentyEightZ_8527 : Nat.Prime 8527 := by norm_num
private theorem prime_twentyEightZ_8861 : Nat.Prime 8861 := by norm_num
private theorem prime_twentyEightZ_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_twentyEightZ_9371 : Nat.Prime 9371 := by norm_num
private theorem prime_twentyEightZ_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_twentyEightZ_10141 : Nat.Prime 10141 := by norm_num
private theorem prime_twentyEightZ_10391 : Nat.Prime 10391 := by norm_num
private theorem prime_twentyEightZ_10601 : Nat.Prime 10601 := by norm_num
private theorem prime_twentyEightZ_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_twentyEightZ_11353 : Nat.Prime 11353 := by norm_num
private theorem prime_twentyEightZ_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_twentyEightZ_12211 : Nat.Prime 12211 := by norm_num
private theorem prime_twentyEightZ_12479 : Nat.Prime 12479 := by norm_num
private theorem prime_twentyEightZ_12589 : Nat.Prime 12589 := by norm_num
private theorem prime_twentyEightZ_13063 : Nat.Prime 13063 := by norm_num
private theorem prime_twentyEightZ_13331 : Nat.Prime 13331 := by norm_num
private theorem prime_twentyEightZ_13789 : Nat.Prime 13789 := by norm_num
private theorem prime_twentyEightZ_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_twentyEightZ_15241 : Nat.Prime 15241 := by norm_num
private theorem prime_twentyEightZ_15319 : Nat.Prime 15319 := by norm_num
private theorem prime_twentyEightZ_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_twentyEightZ_16631 : Nat.Prime 16631 := by norm_num
private theorem prime_twentyEightZ_16963 : Nat.Prime 16963 := by norm_num
private theorem prime_twentyEightZ_17747 : Nat.Prime 17747 := by norm_num
private theorem prime_twentyEightZ_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_twentyEightZ_19249 : Nat.Prime 19249 := by norm_num
private theorem prime_twentyEightZ_19379 : Nat.Prime 19379 := by norm_num
private theorem prime_twentyEightZ_19391 : Nat.Prime 19391 := by norm_num
private theorem prime_twentyEightZ_19801 : Nat.Prime 19801 := by norm_num
private theorem prime_twentyEightZ_20549 : Nat.Prime 20549 := by norm_num
private theorem prime_twentyEightZ_20749 : Nat.Prime 20749 := by norm_num
private theorem prime_twentyEightZ_22279 : Nat.Prime 22279 := by norm_num
private theorem prime_twentyEightZ_22543 : Nat.Prime 22543 := by norm_num
private theorem prime_twentyEightZ_23227 : Nat.Prime 23227 := by norm_num
private theorem prime_twentyEightZ_25457 : Nat.Prime 25457 := by norm_num
private theorem prime_twentyEightZ_26449 : Nat.Prime 26449 := by norm_num
private theorem prime_twentyEightZ_26641 : Nat.Prime 26641 := by norm_num
private theorem prime_twentyEightZ_28279 : Nat.Prime 28279 := by norm_num
private theorem prime_twentyEightZ_28759 : Nat.Prime 28759 := by norm_num
private theorem prime_twentyEightZ_29867 : Nat.Prime 29867 := by norm_num
private theorem prime_twentyEightZ_31079 : Nat.Prime 31079 := by norm_num
private theorem prime_twentyEightZ_33347 : Nat.Prime 33347 := by norm_num
private theorem prime_twentyEightZ_33811 : Nat.Prime 33811 := by norm_num
private theorem prime_twentyEightZ_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_twentyEightZ_35447 : Nat.Prime 35447 := by norm_num
private theorem prime_twentyEightZ_35747 : Nat.Prime 35747 := by norm_num
private theorem prime_twentyEightZ_37223 : Nat.Prime 37223 := by norm_num
private theorem prime_twentyEightZ_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_twentyEightZ_39581 : Nat.Prime 39581 := by norm_num
private theorem prime_twentyEightZ_40433 : Nat.Prime 40433 := by norm_num
private theorem prime_twentyEightZ_42463 : Nat.Prime 42463 := by norm_num
private theorem prime_twentyEightZ_43331 : Nat.Prime 43331 := by norm_num
private theorem prime_twentyEightZ_43591 : Nat.Prime 43591 := by norm_num
private theorem prime_twentyEightZ_44797 : Nat.Prime 44797 := by norm_num
private theorem prime_twentyEightZ_46507 : Nat.Prime 46507 := by norm_num
private theorem prime_twentyEightZ_47939 : Nat.Prime 47939 := by norm_num
private theorem prime_twentyEightZ_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_twentyEightZ_55663 : Nat.Prime 55663 := by norm_num
private theorem prime_twentyEightZ_60427 : Nat.Prime 60427 := by norm_num
private theorem prime_twentyEightZ_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_twentyEightZ_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_twentyEightZ_71563 : Nat.Prime 71563 := by norm_num
private theorem prime_twentyEightZ_72089 : Nat.Prime 72089 := by norm_num
private theorem prime_twentyEightZ_72973 : Nat.Prime 72973 := by norm_num
private theorem prime_twentyEightZ_76441 : Nat.Prime 76441 := by norm_num
private theorem prime_twentyEightZ_90617 : Nat.Prime 90617 := by norm_num
private theorem prime_twentyEightZ_91229 : Nat.Prime 91229 := by norm_num
private theorem prime_twentyEightZ_93199 : Nat.Prime 93199 := by norm_num
private theorem prime_twentyEightZ_93787 : Nat.Prime 93787 := by norm_num
private theorem prime_twentyEightZ_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_twentyEightZ_111869 : Nat.Prime 111869 := by norm_num
private theorem prime_twentyEightZ_112573 : Nat.Prime 112573 := by norm_num
private theorem prime_twentyEightZ_116443 : Nat.Prime 116443 := by norm_num
private theorem prime_twentyEightZ_118399 : Nat.Prime 118399 := by norm_num
private theorem prime_twentyEightZ_127241 : Nat.Prime 127241 := by norm_num
private theorem prime_twentyEightZ_127487 : Nat.Prime 127487 := by norm_num
private theorem prime_twentyEightZ_135571 : Nat.Prime 135571 := by norm_num
private theorem prime_twentyEightZ_137251 : Nat.Prime 137251 := by norm_num
private theorem prime_twentyEightZ_137507 : Nat.Prime 137507 := by norm_num
private theorem prime_twentyEightZ_148537 : Nat.Prime 148537 := by norm_num
private theorem prime_twentyEightZ_149153 : Nat.Prime 149153 := by norm_num
private theorem prime_twentyEightZ_151939 : Nat.Prime 151939 := by norm_num
private theorem prime_twentyEightZ_157177 : Nat.Prime 157177 := by norm_num
private theorem prime_twentyEightZ_162713 : Nat.Prime 162713 := by norm_num
private theorem prime_twentyEightZ_163003 : Nat.Prime 163003 := by norm_num
private theorem prime_twentyEightZ_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_twentyEightZ_164011 : Nat.Prime 164011 := by norm_num
private theorem prime_twentyEightZ_165059 : Nat.Prime 165059 := by norm_num
private theorem prime_twentyEightZ_178183 : Nat.Prime 178183 := by norm_num
private theorem prime_twentyEightZ_189853 : Nat.Prime 189853 := by norm_num
private theorem prime_twentyEightZ_191599 : Nat.Prime 191599 := by norm_num
private theorem prime_twentyEightZ_195271 : Nat.Prime 195271 := by norm_num
private theorem prime_twentyEightZ_201823 : Nat.Prime 201823 := by norm_num
private theorem prime_twentyEightZ_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_twentyEightZ_212981 : Nat.Prime 212981 := by norm_num
private theorem prime_twentyEightZ_215497 : Nat.Prime 215497 := by norm_num
private theorem prime_twentyEightZ_215893 : Nat.Prime 215893 := by norm_num
private theorem prime_twentyEightZ_218857 : Nat.Prime 218857 := by norm_num
private theorem prime_twentyEightZ_221657 : Nat.Prime 221657 := by norm_num
private theorem prime_twentyEightZ_225109 : Nat.Prime 225109 := by norm_num
private theorem prime_twentyEightZ_230291 : Nat.Prime 230291 := by norm_num
private theorem prime_twentyEightZ_239069 : Nat.Prime 239069 := by norm_num
private theorem prime_twentyEightZ_275491 : Nat.Prime 275491 := by norm_num
private theorem prime_twentyEightZ_278561 : Nat.Prime 278561 := by norm_num
private theorem prime_twentyEightZ_293147 : Nat.Prime 293147 := by norm_num
private theorem prime_twentyEightZ_295439 : Nat.Prime 295439 := by norm_num
private theorem prime_twentyEightZ_311677 : Nat.Prime 311677 := by norm_num
private theorem prime_twentyEightZ_316097 : Nat.Prime 316097 := by norm_num
private theorem prime_twentyEightZ_317971 : Nat.Prime 317971 := by norm_num
private theorem prime_twentyEightZ_343559 : Nat.Prime 343559 := by norm_num
private theorem prime_twentyEightZ_344543 : Nat.Prime 344543 := by norm_num
private theorem prime_twentyEightZ_360037 : Nat.Prime 360037 := by norm_num
private theorem prime_twentyEightZ_363611 : Nat.Prime 363611 := by norm_num
private theorem prime_twentyEightZ_367219 : Nat.Prime 367219 := by norm_num
private theorem prime_twentyEightZ_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_twentyEightZ_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_twentyEightZ_398473 : Nat.Prime 398473 := by norm_num
private theorem prime_twentyEightZ_413869 : Nat.Prime 413869 := by norm_num
private theorem prime_twentyEightZ_425681 : Nat.Prime 425681 := by norm_num
private theorem prime_twentyEightZ_431891 : Nat.Prime 431891 := by norm_num
private theorem prime_twentyEightZ_452533 : Nat.Prime 452533 := by norm_num
private theorem prime_twentyEightZ_492979 : Nat.Prime 492979 := by norm_num
private theorem prime_twentyEightZ_502093 : Nat.Prime 502093 := by norm_num
private theorem prime_twentyEightZ_509879 : Nat.Prime 509879 := by norm_num
private theorem prime_twentyEightZ_512903 : Nat.Prime 512903 := by norm_num
private theorem prime_twentyEightZ_518657 : Nat.Prime 518657 := by norm_num
private theorem prime_twentyEightZ_576509 : Nat.Prime 576509 := by norm_num
private theorem prime_twentyEightZ_596081 : Nat.Prime 596081 := by norm_num
private theorem prime_twentyEightZ_608873 : Nat.Prime 608873 := by norm_num
private theorem prime_twentyEightZ_679153 : Nat.Prime 679153 := by norm_num
private theorem prime_twentyEightZ_692663 : Nat.Prime 692663 := by norm_num
private theorem prime_twentyEightZ_715651 : Nat.Prime 715651 := by norm_num
private theorem prime_twentyEightZ_727369 : Nat.Prime 727369 := by norm_num
private theorem prime_twentyEightZ_758159 : Nat.Prime 758159 := by norm_num
private theorem prime_twentyEightZ_888691 : Nat.Prime 888691 := by norm_num
private theorem prime_twentyEightZ_951637 : Nat.Prime 951637 := by norm_num
private theorem prime_twentyEightZ_1003627 : Nat.Prime 1003627 := by norm_num
private theorem prime_twentyEightZ_1127333 : Nat.Prime 1127333 := by norm_num
private theorem prime_twentyEightZ_1173959 : Nat.Prime 1173959 := by norm_num
private theorem prime_twentyEightZ_1179173 : Nat.Prime 1179173 := by norm_num
private theorem prime_twentyEightZ_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_twentyEightZ_1229531 : Nat.Prime 1229531 := by norm_num
private theorem prime_twentyEightZ_1255301 : Nat.Prime 1255301 := by norm_num
private theorem prime_twentyEightZ_1286149 : Nat.Prime 1286149 := by norm_num
private theorem prime_twentyEightZ_1346333 : Nat.Prime 1346333 := by norm_num
private theorem prime_twentyEightZ_1453129 : Nat.Prime 1453129 := by norm_num
private theorem prime_twentyEightZ_1489003 : Nat.Prime 1489003 := by norm_num
private theorem prime_twentyEightZ_1612937 : Nat.Prime 1612937 := by norm_num
private theorem prime_twentyEightZ_1693169 : Nat.Prime 1693169 := by norm_num
private theorem prime_twentyEightZ_1768411 : Nat.Prime 1768411 := by norm_num
private theorem prime_twentyEightZ_1865881 : Nat.Prime 1865881 := by norm_num
private theorem prime_twentyEightZ_1879601 : Nat.Prime 1879601 := by norm_num
private theorem prime_twentyEightZ_1957301 : Nat.Prime 1957301 := by norm_num
private theorem prime_twentyEightZ_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_twentyEightZ_2290081 : Nat.Prime 2290081 := by norm_num
private theorem prime_twentyEightZ_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_twentyEightZ_2633923 : Nat.Prime 2633923 := by norm_num
private theorem prime_twentyEightZ_2846287 : Nat.Prime 2846287 := by norm_num
private theorem prime_twentyEightZ_2993957 : Nat.Prime 2993957 := by norm_num
private theorem prime_twentyEightZ_3015373 : Nat.Prime 3015373 := by norm_num
private theorem prime_twentyEightZ_3414581 : Nat.Prime 3414581 := by norm_num
private theorem prime_twentyEightZ_3532679 : Nat.Prime 3532679 := by norm_num
private theorem prime_twentyEightZ_3600853 : Nat.Prime 3600853 := by norm_num
private theorem prime_twentyEightZ_3779417 : Nat.Prime 3779417 := by norm_num
private theorem prime_twentyEightZ_3871433 : Nat.Prime 3871433 := by norm_num
private theorem prime_twentyEightZ_4562351 : Nat.Prime 4562351 := by norm_num
private theorem prime_twentyEightZ_5101879 : Nat.Prime 5101879 := by norm_num
private theorem prime_twentyEightZ_5301631 : Nat.Prime 5301631 := by norm_num
private theorem prime_twentyEightZ_5572883 : Nat.Prime 5572883 := by norm_num
private theorem prime_twentyEightZ_5698267 : Nat.Prime 5698267 := by norm_num
private theorem prime_twentyEightZ_5826967 : Nat.Prime 5826967 := by norm_num
private theorem prime_twentyEightZ_5944361 : Nat.Prime 5944361 := by norm_num
private theorem prime_twentyEightZ_6135331 : Nat.Prime 6135331 := by norm_num
private theorem prime_twentyEightZ_6470753 : Nat.Prime 6470753 := by norm_num
private theorem prime_twentyEightZ_6475879 : Nat.Prime 6475879 := by norm_num
private theorem prime_twentyEightZ_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_twentyEightZ_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_twentyEightZ_7368811 : Nat.Prime 7368811 := by norm_num
private theorem prime_twentyEightZ_7780667 : Nat.Prime 7780667 := by norm_num
private theorem prime_twentyEightZ_7978459 : Nat.Prime 7978459 := by norm_num
private theorem prime_twentyEightZ_8081747 : Nat.Prime 8081747 := by norm_num
private theorem prime_twentyEightZ_8522119 : Nat.Prime 8522119 := by norm_num
private theorem prime_twentyEightZ_9167321 : Nat.Prime 9167321 := by norm_num
private theorem prime_twentyEightZ_9840643 : Nat.Prime 9840643 := by norm_num
private theorem prime_twentyEightZ_10049639 : Nat.Prime 10049639 := by norm_num
private theorem prime_twentyEightZ_10167809 : Nat.Prime 10167809 := by norm_num
private theorem prime_twentyEightZ_11152399 : Nat.Prime 11152399 := by norm_num
private theorem prime_twentyEightZ_11531881 : Nat.Prime 11531881 := by norm_num
private theorem prime_twentyEightZ_12136613 : Nat.Prime 12136613 := by norm_num
private theorem prime_twentyEightZ_12137267 : Nat.Prime 12137267 := by norm_num
private theorem prime_twentyEightZ_12815969 : Nat.Prime 12815969 := by norm_num
private theorem prime_twentyEightZ_13166369 : Nat.Prime 13166369 := by norm_num
private theorem prime_twentyEightZ_14969873 : Nat.Prime 14969873 := by norm_num
private theorem prime_twentyEightZ_16649617 : Nat.Prime 16649617 := by norm_num
private theorem prime_twentyEightZ_16698589 : Nat.Prime 16698589 := by norm_num
private theorem prime_twentyEightZ_17052281 : Nat.Prime 17052281 := by norm_num
private theorem prime_twentyEightZ_17290739 : Nat.Prime 17290739 := by norm_num
private theorem prime_twentyEightZ_18223631 : Nat.Prime 18223631 := by norm_num
private theorem prime_twentyEightZ_19742057 : Nat.Prime 19742057 := by norm_num
private theorem prime_twentyEightZ_20315369 : Nat.Prime 20315369 := by norm_num
private theorem prime_twentyEightZ_20980153 : Nat.Prime 20980153 := by norm_num
private theorem prime_twentyEightZ_22951043 : Nat.Prime 22951043 := by norm_num
private theorem prime_twentyEightZ_27075547 : Nat.Prime 27075547 := by norm_num
private theorem prime_twentyEightZ_27757949 : Nat.Prime 27757949 := by norm_num

private theorem prime_twentyEightZ_31913837 : Nat.Prime 31913837 := by
  apply lucas_primality 31913837 (2 : ZMod 31913837)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) = 31913837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7978459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31913837) ^ 15956918 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31913837) ^ 4 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_35853943 : Nat.Prime 35853943 := by
  apply lucas_primality 35853943 (3 : ZMod 35853943)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (983, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_983
      · exact prime_twentyEightZ_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853943) ^ 17926971 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 11951314 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 36474 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853943) ^ 5898 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_39051989 : Nat.Prime 39051989 := by
  apply lucas_primality 39051989 (2 : ZMod 39051989)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (137507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (137507, 1)] : List FactorBlock).map factorBlockValue).prod) = 39051989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_71
      · exact prime_twentyEightZ_137507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39051989) ^ 19525994 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39051989) ^ 550028 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39051989) ^ 284 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_45885799 : Nat.Prime 45885799 := by
  apply lucas_primality 45885799 (7 : ZMod 45885799)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) = 45885799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_6389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 45885799) ^ 22942899 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 15295266 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 6555114 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 2415042 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 7182 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_56438293 : Nat.Prime 56438293 := by
  apply lucas_primality 56438293 (2 : ZMod 56438293)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (127, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (127, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) = 56438293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_127
      · exact prime_twentyEightZ_1277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56438293) ^ 28219146 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56438293) ^ 18812764 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56438293) ^ 1946148 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56438293) ^ 444396 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56438293) ^ 44196 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_61623641 : Nat.Prime 61623641 := by
  apply lucas_primality 61623641 (11 : ZMod 61623641)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (17, 1), (6971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (17, 1), (6971, 1)] : List FactorBlock).map factorBlockValue).prod) = 61623641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_6971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 61623641) ^ 30811820 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 61623641) ^ 12324728 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 61623641) ^ 4740280 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 61623641) ^ 3624920 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 61623641) ^ 8840 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_72158159 : Nat.Prime 72158159 := by
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod) = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_1901
      · exact prime_twentyEightZ_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 72158159) ^ 36079079 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 37958 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 72158159) ^ 3802 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_75709871 : Nat.Prime 75709871 := by
  apply lucas_primality 75709871 (19 : ZMod 75709871)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (398473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (398473, 1)] : List FactorBlock).map factorBlockValue).prod) = 75709871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_398473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 75709871) ^ 37854935 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 75709871) ^ 15141974 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 75709871) ^ 3984730 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 75709871) ^ 190 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_82122319 : Nat.Prime 82122319 := by
  apply lucas_primality 82122319 (6 : ZMod 82122319)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4562351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4562351, 1)] : List FactorBlock).map factorBlockValue).prod) = 82122319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_4562351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 82122319) ^ 41061159 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 82122319) ^ 27374106 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 82122319) ^ 18 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_83313799 : Nat.Prime 83313799 := by
  apply lucas_primality 83313799 (7 : ZMod 83313799)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (295439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (295439, 1)] : List FactorBlock).map factorBlockValue).prod) = 83313799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_295439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 83313799) ^ 41656899 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 83313799) ^ 27771266 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 83313799) ^ 1772634 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 83313799) ^ 282 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_89562289 : Nat.Prime 89562289 := by
  apply lucas_primality 89562289 (13 : ZMod 89562289)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1865881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1865881, 1)] : List FactorBlock).map factorBlockValue).prod) = 89562289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_1865881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 89562289) ^ 44781144 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 89562289) ^ 29854096 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 89562289) ^ 48 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_90030431 : Nat.Prime 90030431 := by
  apply lucas_primality 90030431 (7 : ZMod 90030431)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1286149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1286149, 1)] : List FactorBlock).map factorBlockValue).prod) = 90030431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_1286149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 90030431) ^ 45015215 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 90030431) ^ 18006086 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 90030431) ^ 12861490 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 90030431) ^ 70 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_90735599 : Nat.Prime 90735599 := by
  apply lucas_primality 90735599 (11 : ZMod 90735599)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (151, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (151, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) = 90735599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_151
      · exact prime_twentyEightZ_13063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 90735599) ^ 45367799 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 3945026 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 600898 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 90735599) ^ 6946 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_94465933 : Nat.Prime 94465933 := by
  apply lucas_primality 94465933 (5 : ZMod 94465933)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (715651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (715651, 1)] : List FactorBlock).map factorBlockValue).prod) = 94465933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_715651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 94465933) ^ 47232966 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 94465933) ^ 31488644 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 94465933) ^ 8587812 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 94465933) ^ 132 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_115318811 : Nat.Prime 115318811 := by
  apply lucas_primality 115318811 (2 : ZMod 115318811)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11531881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11531881, 1)] : List FactorBlock).map factorBlockValue).prod) = 115318811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_11531881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 115318811) ^ 57659405 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 115318811) ^ 23063762 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 115318811) ^ 10 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_133260553 : Nat.Prime 133260553 := by
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod) = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 133260553) ^ 66630276 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 44420184 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 7838856 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 133260553) ^ 11016 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_143078893 : Nat.Prime 143078893 := by
  apply lucas_primality 143078893 (5 : ZMod 143078893)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 1), (89, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 1), (89, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) = 143078893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_89
      · exact prime_twentyEightZ_641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 143078893) ^ 71539446 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 47692964 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 13007172 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 7530468 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 1607628 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 223212 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_144417341 : Nat.Prime 144417341 := by
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod) = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144417341) ^ 72208670 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 28883468 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 144417341) ^ 20 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_153198571 : Nat.Prime 153198571 := by
  apply lucas_primality 153198571 (3 : ZMod 153198571)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (479, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (479, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 153198571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_479
      · exact prime_twentyEightZ_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 153198571) ^ 76599285 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 153198571) ^ 51066190 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 153198571) ^ 30639714 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 153198571) ^ 21885510 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 153198571) ^ 319830 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 153198571) ^ 100590 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_153791629 : Nat.Prime 153791629 := by
  apply lucas_primality 153791629 (2 : ZMod 153791629)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12815969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12815969, 1)] : List FactorBlock).map factorBlockValue).prod) = 153791629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_12815969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 153791629) ^ 76895814 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 153791629) ^ 51263876 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 153791629) ^ 12 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_169985287 : Nat.Prime 169985287 := by
  apply lucas_primality 169985287 (3 : ZMod 169985287)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (307, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (307, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) = 169985287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_307
      · exact prime_twentyEightZ_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 169985287) ^ 84992643 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 56661762 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 8946594 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 553698 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 104994 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_172809677 : Nat.Prime 172809677 := by
  apply lucas_primality 172809677 (5 : ZMod 172809677)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (359, 1), (9257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (359, 1), (9257, 1)] : List FactorBlock).map factorBlockValue).prod) = 172809677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_359
      · exact prime_twentyEightZ_9257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 172809677) ^ 86404838 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 172809677) ^ 13293052 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 172809677) ^ 481364 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 172809677) ^ 18668 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_189168241 : Nat.Prime 189168241 := by
  apply lucas_primality 189168241 (13 : ZMod 189168241)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (503, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (503, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) = 189168241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_503
      · exact prime_twentyEightZ_1567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 189168241) ^ 94584120 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 189168241) ^ 63056080 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 189168241) ^ 37833648 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 189168241) ^ 376080 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 189168241) ^ 120720 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_189324997 : Nat.Prime 189324997 := by
  apply lucas_primality 189324997 (5 : ZMod 189324997)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (127, 1), (17747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (127, 1), (17747, 1)] : List FactorBlock).map factorBlockValue).prod) = 189324997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_127
      · exact prime_twentyEightZ_17747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 189324997) ^ 94662498 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 189324997) ^ 63108332 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 189324997) ^ 27046428 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 189324997) ^ 1490748 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 189324997) ^ 10668 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_202582477 : Nat.Prime 202582477 := by
  apply lucas_primality 202582477 (5 : ZMod 202582477)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (137251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (137251, 1)] : List FactorBlock).map factorBlockValue).prod) = 202582477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_137251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 202582477) ^ 101291238 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 202582477) ^ 67527492 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 202582477) ^ 4941036 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 202582477) ^ 1476 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_209801531 : Nat.Prime 209801531 := by
  apply lucas_primality 209801531 (6 : ZMod 209801531)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (20980153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (20980153, 1)] : List FactorBlock).map factorBlockValue).prod) = 209801531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_20980153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 209801531) ^ 104900765 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 209801531) ^ 41960306 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 209801531) ^ 10 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_216317813 : Nat.Prime 216317813 := by
  apply lucas_primality 216317813 (2 : ZMod 216317813)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) = 216317813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_2846287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216317813) ^ 108158906 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 11385148 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 76 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_218470807 : Nat.Prime 218470807 := by
  apply lucas_primality 218470807 (3 : ZMod 218470807)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (12137267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (12137267, 1)] : List FactorBlock).map factorBlockValue).prod) = 218470807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_12137267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 218470807) ^ 109235403 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 218470807) ^ 72823602 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 218470807) ^ 18 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_229713433 : Nat.Prime 229713433 := by
  apply lucas_primality 229713433 (5 : ZMod 229713433)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (59, 1), (12479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (59, 1), (12479, 1)] : List FactorBlock).map factorBlockValue).prod) = 229713433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_12479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 229713433) ^ 114856716 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 229713433) ^ 76571144 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 229713433) ^ 17670264 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 229713433) ^ 3893448 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 229713433) ^ 18408 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_191
      · exact prime_twentyEightZ_383
      · exact prime_twentyEightZ_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_267586283 : Nat.Prime 267586283 := by
  apply lucas_primality 267586283 (2 : ZMod 267586283)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (679153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (679153, 1)] : List FactorBlock).map factorBlockValue).prod) = 267586283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_197
      · exact prime_twentyEightZ_679153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 267586283) ^ 133793141 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 267586283) ^ 1358306 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 267586283) ^ 394 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_277100209 : Nat.Prime 277100209 := by
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_67
      · exact prime_twentyEightZ_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 277100209) ^ 138550104 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 92366736 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 39585744 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 25190928 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 4135824 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 277100209) ^ 742896 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_286464551 : Nat.Prime 286464551 := by
  apply lucas_primality 286464551 (7 : ZMod 286464551)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1303, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1303, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 286464551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_1303
      · exact prime_twentyEightZ_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 286464551) ^ 143232275 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 57292910 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 219850 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 65150 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_292575589 : Nat.Prime 292575589 := by
  apply lucas_primality 292575589 (2 : ZMod 292575589)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 1), (283, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 1), (283, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 292575589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_101
      · exact prime_twentyEightZ_283
      · exact prime_twentyEightZ_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 292575589) ^ 146287794 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 292575589) ^ 97525196 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 292575589) ^ 2896788 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 292575589) ^ 1033836 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 292575589) ^ 342996 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_359085967 : Nat.Prime 359085967 := by
  apply lucas_primality 359085967 (3 : ZMod 359085967)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (281, 1), (212981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (281, 1), (212981, 1)] : List FactorBlock).map factorBlockValue).prod) = 359085967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_281
      · exact prime_twentyEightZ_212981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 359085967) ^ 179542983 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 359085967) ^ 119695322 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 359085967) ^ 1277886 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 359085967) ^ 1686 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_381350491 : Nat.Prime 381350491 := by
  apply lucas_primality 381350491 (2 : ZMod 381350491)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (343559, 1)] : List FactorBlock).map factorBlockValue).prod) = 381350491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_343559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 381350491) ^ 190675245 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 127116830 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 76270098 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 10306770 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 381350491) ^ 1110 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_495184799 : Nat.Prime 495184799 := by
  apply lucas_primality 495184799 (7 : ZMod 495184799)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (79, 1), (76441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (79, 1), (76441, 1)] : List FactorBlock).map factorBlockValue).prod) = 495184799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_79
      · exact prime_twentyEightZ_76441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 495184799) ^ 247592399 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 495184799) ^ 12077678 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 495184799) ^ 6268162 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 495184799) ^ 6478 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_545672993 : Nat.Prime 545672993 := by
  apply lucas_primality 545672993 (3 : ZMod 545672993)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17052281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17052281, 1)] : List FactorBlock).map factorBlockValue).prod) = 545672993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_17052281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 545672993) ^ 272836496 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 545672993) ^ 32 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_550990241 : Nat.Prime 550990241 := by
  apply lucas_primality 550990241 (3 : ZMod 550990241)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) = 550990241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_79
      · exact prime_twentyEightZ_43591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 550990241) ^ 275495120 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 110198048 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 6974560 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 12640 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_580732433 : Nat.Prime 580732433 := by
  apply lucas_primality 580732433 (3 : ZMod 580732433)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (131, 1), (39581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (131, 1), (39581, 1)] : List FactorBlock).map factorBlockValue).prod) = 580732433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_131
      · exact prime_twentyEightZ_39581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 580732433) ^ 290366216 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 580732433) ^ 82961776 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 580732433) ^ 4433072 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 580732433) ^ 14672 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_587007193 : Nat.Prime 587007193 := by
  apply lucas_primality 587007193 (5 : ZMod 587007193)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2003, 1), (12211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2003, 1), (12211, 1)] : List FactorBlock).map factorBlockValue).prod) = 587007193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_2003
      · exact prime_twentyEightZ_12211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 587007193) ^ 293503596 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 587007193) ^ 195669064 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 587007193) ^ 293064 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 587007193) ^ 48072 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_898397459 : Nat.Prime 898397459 := by
  apply lucas_primality 898397459 (2 : ZMod 898397459)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (9167321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (9167321, 1)] : List FactorBlock).map factorBlockValue).prod) = 898397459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_9167321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 898397459) ^ 449198729 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 898397459) ^ 128342494 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 898397459) ^ 98 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1071521281 : Nat.Prime 1071521281 := by
  apply lucas_primality 1071521281 (11 : ZMod 1071521281)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (5, 1), (46507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (5, 1), (46507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1071521281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_46507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1071521281) ^ 535760640 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1071521281) ^ 357173760 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1071521281) ^ 214304256 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1071521281) ^ 23040 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1088310731 : Nat.Prime 1088310731 := by
  apply lucas_primality 1088310731 (7 : ZMod 1088310731)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (2239, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (2239, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088310731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_2239
      · exact prime_twentyEightZ_3739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1088310731) ^ 544155365 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 217662146 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 83716210 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 486070 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 291070 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_113
      · exact prime_twentyEightZ_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1255074433 : Nat.Prime 1255074433 := by
  apply lucas_primality 1255074433 (10 : ZMod 1255074433)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255074433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1255074433) ^ 627537216 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 418358144 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 40486272 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 21272448 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 1255074433) ^ 702336 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1366656409 : Nat.Prime 1366656409 := by
  apply lucas_primality 1366656409 (7 : ZMod 1366656409)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (179, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (179, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1366656409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_179
      · exact prime_twentyEightZ_2719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1366656409) ^ 683328204 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1366656409) ^ 455552136 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1366656409) ^ 105127416 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1366656409) ^ 7634952 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1366656409) ^ 502632 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1440461809 : Nat.Prime 1440461809 := by
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_61
      · exact prime_twentyEightZ_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1440461809) ^ 720230904 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 480153936 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 23614128 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1440461809) ^ 8784 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1514175419 : Nat.Prime 1514175419 := by
  apply lucas_primality 1514175419 (2 : ZMod 1514175419)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (239, 1), (452533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (239, 1), (452533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514175419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_239
      · exact prime_twentyEightZ_452533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1514175419) ^ 757087709 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514175419) ^ 216310774 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514175419) ^ 6335462 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514175419) ^ 3346 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1590164911 : Nat.Prime 1590164911 := by
  apply lucas_primality 1590164911 (3 : ZMod 1590164911)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1590164911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1590164911) ^ 795082455 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 530054970 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 318032982 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 83692890 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 42977430 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 38784510 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 2594070 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1698045001 : Nat.Prime 1698045001 := by
  apply lucas_primality 1698045001 (29 : ZMod 1698045001)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 4), (17, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 4), (17, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1698045001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_6659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 1698045001) ^ 849022500 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 1698045001) ^ 566015000 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 1698045001) ^ 339609000 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 1698045001) ^ 99885000 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 1698045001) ^ 255000 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1796794919 : Nat.Prime 1796794919 := by
  apply lucas_primality 1796794919 (29 : ZMod 1796794919)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (898397459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (898397459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1796794919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_898397459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (29 : ZMod 1796794919) ^ 898397459 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 1796794919) ^ 2 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3139143389 : Nat.Prime 3139143389 := by
  apply lucas_primality 3139143389 (2 : ZMod 3139143389)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 3139143389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_359
      · exact prime_twentyEightZ_677
      · exact prime_twentyEightZ_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3139143389) ^ 1569571694 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 8744132 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 4636844 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 972172 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3198253273 : Nat.Prime 3198253273 := by
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod) = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3198253273) ^ 1599126636 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 1066084424 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3198253273) ^ 24 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3522043159 : Nat.Prime 3522043159 := by
  apply lucas_primality 3522043159 (3 : ZMod 3522043159)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (587007193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (587007193, 1)] : List FactorBlock).map factorBlockValue).prod) = 3522043159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_587007193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3522043159) ^ 1761021579 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3522043159) ^ 1174014386 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3522043159) ^ 6 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3813504911 : Nat.Prime 3813504911 := by
  apply lucas_primality 3813504911 (17 : ZMod 3813504911)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (381350491, 1)] : List FactorBlock).map factorBlockValue).prod) = 3813504911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_381350491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 3813504911) ^ 1906752455 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 762700982 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 3813504911) ^ 10 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_4024245521 : Nat.Prime 4024245521 := by
  apply lucas_primality 4024245521 (3 : ZMod 4024245521)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (233, 1), (215893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (233, 1), (215893, 1)] : List FactorBlock).map factorBlockValue).prod) = 4024245521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_233
      · exact prime_twentyEightZ_215893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4024245521) ^ 2012122760 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4024245521) ^ 804849104 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4024245521) ^ 17271440 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4024245521) ^ 18640 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_4942603493 : Nat.Prime 4942603493 := by
  apply lucas_primality 4942603493 (2 : ZMod 4942603493)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (107, 1), (502093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (107, 1), (502093, 1)] : List FactorBlock).map factorBlockValue).prod) = 4942603493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_107
      · exact prime_twentyEightZ_502093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4942603493) ^ 2471301746 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4942603493) ^ 214895804 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4942603493) ^ 46192556 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4942603493) ^ 9844 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_5252180671 : Nat.Prime 5252180671 := by
  apply lucas_primality 5252180671 (11 : ZMod 5252180671)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (1768411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (1768411, 1)] : List FactorBlock).map factorBlockValue).prod) = 5252180671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_1768411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5252180671) ^ 2626090335 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 5252180671) ^ 1750726890 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 5252180671) ^ 1050436134 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 5252180671) ^ 477470970 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 5252180671) ^ 2970 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_5741877473 : Nat.Prime 5741877473 := by
  apply lucas_primality 5741877473 (3 : ZMod 5741877473)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (41, 1), (101, 1), (43331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (41, 1), (101, 1), (43331, 1)] : List FactorBlock).map factorBlockValue).prod) = 5741877473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_101
      · exact prime_twentyEightZ_43331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5741877473) ^ 2870938736 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5741877473) ^ 140045792 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5741877473) ^ 56850272 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5741877473) ^ 132512 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_7652554093 : Nat.Prime 7652554093 := by
  apply lucas_primality 7652554093 (5 : ZMod 7652554093)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (2993957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (2993957, 1)] : List FactorBlock).map factorBlockValue).prod) = 7652554093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_71
      · exact prime_twentyEightZ_2993957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7652554093) ^ 3826277046 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 2550851364 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 107782452 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 2556 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_8696692033 : Nat.Prime 8696692033 := by
  apply lucas_primality 8696692033 (17 : ZMod 8696692033)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod) = 8696692033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_6470753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 8696692033) ^ 4348346016 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 2898897344 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1242384576 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1344 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_9361944367 : Nat.Prime 9361944367 := by
  apply lucas_primality 9361944367 (5 : ZMod 9361944367)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (82122319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (82122319, 1)] : List FactorBlock).map factorBlockValue).prod) = 9361944367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_82122319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9361944367) ^ 4680972183 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9361944367) ^ 3120648122 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9361944367) ^ 492733914 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9361944367) ^ 114 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_14853048211 : Nat.Prime 14853048211 := by
  apply lucas_primality 14853048211 (2 : ZMod 14853048211)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (173, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (173, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) = 14853048211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_173
      · exact prime_twentyEightZ_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14853048211) ^ 7426524105 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 4951016070 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 2970609642 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 2121864030 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 1350277110 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 1142542170 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 85855770 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 15585570 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_16539367177 : Nat.Prime 16539367177 := by
  apply lucas_primality 16539367177 (5 : ZMod 16539367177)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (229713433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (229713433, 1)] : List FactorBlock).map factorBlockValue).prod) = 16539367177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_229713433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16539367177) ^ 8269683588 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16539367177) ^ 5513122392 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16539367177) ^ 72 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_17037864143 : Nat.Prime 17037864143 := by
  apply lucas_primality 17037864143 (5 : ZMod 17037864143)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (709, 1), (22543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (709, 1), (22543, 1)] : List FactorBlock).map factorBlockValue).prod) = 17037864143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_709
      · exact prime_twentyEightZ_22543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17037864143) ^ 8518932071 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 1310604934 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 415557662 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 24030838 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 755794 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_17483007257 : Nat.Prime 17483007257 := by
  apply lucas_primality 17483007257 (6 : ZMod 17483007257)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod) = 17483007257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_492979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17483007257) ^ 8741503628 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1589364296 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 1344846712 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 563967976 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 17483007257) ^ 35464 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_17948527271 : Nat.Prime 17948527271 := by
  apply lucas_primality 17948527271 (19 : ZMod 17948527271)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (94465933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (94465933, 1)] : List FactorBlock).map factorBlockValue).prod) = 17948527271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_94465933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 17948527271) ^ 8974263635 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 17948527271) ^ 3589705454 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 17948527271) ^ 944659330 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 17948527271) ^ 190 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_20319607769 : Nat.Prime 20319607769 := by
  apply lucas_primality 20319607769 (3 : ZMod 20319607769)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5881, 1), (431891, 1)] : List FactorBlock).map factorBlockValue).prod) = 20319607769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5881
      · exact prime_twentyEightZ_431891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20319607769) ^ 10159803884 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 3455128 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 20319607769) ^ 47048 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_20597651827 : Nat.Prime 20597651827 := by
  apply lucas_primality 20597651827 (5 : ZMod 20597651827)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (149, 1), (283, 1), (4789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (149, 1), (283, 1), (4789, 1)] : List FactorBlock).map factorBlockValue).prod) = 20597651827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_149
      · exact prime_twentyEightZ_283
      · exact prime_twentyEightZ_4789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 20597651827) ^ 10298825913 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20597651827) ^ 6865883942 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20597651827) ^ 1211626578 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20597651827) ^ 138239274 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20597651827) ^ 72783222 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20597651827) ^ 4301034 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_24913302187 : Nat.Prime 24913302187 := by
  apply lucas_primality 24913302187 (2 : ZMod 24913302187)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 24913302187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_487
      · exact prime_twentyEightZ_2621
      · exact prime_twentyEightZ_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24913302187) ^ 12456651093 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 8304434062 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 51156678 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 9505266 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 7658562 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_31949565563 : Nat.Prime 31949565563 := by
  apply lucas_primality 31949565563 (2 : ZMod 31949565563)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (75709871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (75709871, 1)] : List FactorBlock).map factorBlockValue).prod) = 31949565563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_211
      · exact prime_twentyEightZ_75709871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31949565563) ^ 15974782781 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31949565563) ^ 151419742 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31949565563) ^ 422 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_36501913991 : Nat.Prime 36501913991 := by
  apply lucas_primality 36501913991 (14 : ZMod 36501913991)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3637, 1), (1003627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3637, 1), (1003627, 1)] : List FactorBlock).map factorBlockValue).prod) = 36501913991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_3637
      · exact prime_twentyEightZ_1003627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 36501913991) ^ 18250956995 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (14 : ZMod 36501913991) ^ 7300382798 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (14 : ZMod 36501913991) ^ 10036270 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (14 : ZMod 36501913991) ^ 36370 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_41082692429 : Nat.Prime 41082692429 := by
  apply lucas_primality 41082692429 (2 : ZMod 41082692429)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (39051989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (39051989, 1)] : List FactorBlock).map factorBlockValue).prod) = 41082692429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_263
      · exact prime_twentyEightZ_39051989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41082692429) ^ 20541346214 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 41082692429) ^ 156207956 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 41082692429) ^ 1052 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_151
      · exact prime_twentyEightZ_479
      · exact prime_twentyEightZ_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_70908014633 : Nat.Prime 70908014633 := by
  apply lucas_primality 70908014633 (3 : ZMod 70908014633)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (4919, 1), (19801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (4919, 1), (19801, 1)] : List FactorBlock).map factorBlockValue).prod) = 70908014633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_4919
      · exact prime_twentyEightZ_19801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70908014633) ^ 35454007316 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 10129716376 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 5454462664 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 14415128 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 70908014633) ^ 3581032 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_73987284121 : Nat.Prime 73987284121 := by
  apply lucas_primality 73987284121 (29 : ZMod 73987284121)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) = 73987284121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_73
      · exact prime_twentyEightZ_367219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 73987284121) ^ 36993642060 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 24662428040 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 14797456824 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 3216838440 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 1013524440 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 201480 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_81554969011 : Nat.Prime 81554969011 := by
  apply lucas_primality 81554969011 (3 : ZMod 81554969011)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (143078893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (143078893, 1)] : List FactorBlock).map factorBlockValue).prod) = 81554969011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_143078893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81554969011) ^ 40777484505 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 27184989670 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 16310993802 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 4292366790 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 570 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_84927410431 : Nat.Prime 84927410431 := by
  apply lucas_primality 84927410431 (6 : ZMod 84927410431)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (67, 1), (692663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (67, 1), (692663, 1)] : List FactorBlock).map factorBlockValue).prod) = 84927410431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_61
      · exact prime_twentyEightZ_67
      · exact prime_twentyEightZ_692663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 84927410431) ^ 42463705215 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 28309136810 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 16985482086 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 1392252630 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 1267573290 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 122610 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_102310987907 : Nat.Prime 102310987907 := by
  apply lucas_primality 102310987907 (2 : ZMod 102310987907)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (7013, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (7013, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) = 102310987907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_7013
      · exact prime_twentyEightZ_13789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102310987907) ^ 51155493953 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 4448303822 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 14588762 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 7419754 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_120863194567 : Nat.Prime 120863194567 := by
  apply lucas_primality 120863194567 (3 : ZMod 120863194567)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod) = 120863194567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_439
      · exact prime_twentyEightZ_45885799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120863194567) ^ 60431597283 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 40287731522 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 275314794 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 2634 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_125934703277 : Nat.Prime 125934703277 := by
  apply lucas_primality 125934703277 (2 : ZMod 125934703277)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157, 1), (241, 1), (701, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157, 1), (241, 1), (701, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) = 125934703277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_157
      · exact prime_twentyEightZ_241
      · exact prime_twentyEightZ_701
      · exact prime_twentyEightZ_1187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125934703277) ^ 62967351638 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 125934703277) ^ 802131868 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 125934703277) ^ 522550636 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 125934703277) ^ 179650076 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 125934703277) ^ 106094948 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_133817607761 : Nat.Prime 133817607761 := by
  apply lucas_primality 133817607761 (3 : ZMod 133817607761)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (227, 1), (7368811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (227, 1), (7368811, 1)] : List FactorBlock).map factorBlockValue).prod) = 133817607761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_227
      · exact prime_twentyEightZ_7368811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 133817607761) ^ 66908803880 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 133817607761) ^ 26763521552 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 133817607761) ^ 589504880 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 133817607761) ^ 18160 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_138448735921 : Nat.Prime 138448735921 := by
  apply lucas_primality 138448735921 (14 : ZMod 138448735921)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (11, 1), (5826967, 1)] : List FactorBlock).map factorBlockValue).prod) = 138448735921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_5826967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 138448735921) ^ 69224367960 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 46149578640 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 27689747184 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 12586248720 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (14 : ZMod 138448735921) ^ 23760 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_152394958517 : Nat.Prime 152394958517 := by
  apply lucas_primality 152394958517 (2 : ZMod 152394958517)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (709, 1), (90617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (709, 1), (90617, 1)] : List FactorBlock).map factorBlockValue).prod) = 152394958517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_593
      · exact prime_twentyEightZ_709
      · exact prime_twentyEightZ_90617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152394958517) ^ 76197479258 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 256989812 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 214943524 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 1681748 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_165143602937 : Nat.Prime 165143602937 := by
  apply lucas_primality 165143602937 (3 : ZMod 165143602937)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (35447, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (35447, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 165143602937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_35447
      · exact prime_twentyEightZ_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 165143602937) ^ 82571801468 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 165143602937) ^ 12703354072 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 165143602937) ^ 4658888 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 165143602937) ^ 3686488 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_189484704379 : Nat.Prime 189484704379 := by
  apply lucas_primality 189484704379 (2 : ZMod 189484704379)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (571, 1), (661, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (571, 1), (661, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) = 189484704379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_571
      · exact prime_twentyEightZ_661
      · exact prime_twentyEightZ_1033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 189484704379) ^ 94742352189 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 189484704379) ^ 63161568126 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 189484704379) ^ 331847118 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 189484704379) ^ 286663698 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 189484704379) ^ 183431466 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_201577281629 : Nat.Prime 201577281629 := by
  apply lucas_primality 201577281629 (2 : ZMod 201577281629)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (23, 1), (115318811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (23, 1), (115318811, 1)] : List FactorBlock).map factorBlockValue).prod) = 201577281629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_115318811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 201577281629) ^ 100788640814 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 201577281629) ^ 10609330612 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 201577281629) ^ 8764229636 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 201577281629) ^ 1748 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_254426385761 : Nat.Prime 254426385761 := by
  apply lucas_primality 254426385761 (3 : ZMod 254426385761)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod) = 254426385761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_1590164911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 254426385761) ^ 127213192880 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 50885277152 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 160 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_277280084413 : Nat.Prime 277280084413 := by
  apply lucas_primality 277280084413 (5 : ZMod 277280084413)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (23, 1), (31, 1), (3600853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (23, 1), (31, 1), (3600853, 1)] : List FactorBlock).map factorBlockValue).prod) = 277280084413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_3600853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 277280084413) ^ 138640042206 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 92426694804 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 12055655844 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 8944518852 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 277280084413) ^ 77004 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_326767060643 : Nat.Prime 326767060643 := by
  apply lucas_primality 326767060643 (2 : ZMod 326767060643)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (14853048211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (14853048211, 1)] : List FactorBlock).map factorBlockValue).prod) = 326767060643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_14853048211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 326767060643) ^ 163383530321 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767060643) ^ 29706096422 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767060643) ^ 22 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_344701622887 : Nat.Prime 344701622887 := by
  apply lucas_primality 344701622887 (3 : ZMod 344701622887)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (37, 1), (409, 1), (165059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (37, 1), (409, 1), (165059, 1)] : List FactorBlock).map factorBlockValue).prod) = 344701622887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_409
      · exact prime_twentyEightZ_165059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 344701622887) ^ 172350811443 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 344701622887) ^ 114900540962 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 344701622887) ^ 14987027082 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 344701622887) ^ 9316260078 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 344701622887) ^ 842791254 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 344701622887) ^ 2088354 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_397
      · exact prime_twentyEightZ_2531
      · exact prime_twentyEightZ_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_521262387533 : Nat.Prime 521262387533 := by
  apply lucas_primality 521262387533 (2 : ZMod 521262387533)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (3522043159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (3522043159, 1)] : List FactorBlock).map factorBlockValue).prod) = 521262387533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_3522043159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 521262387533) ^ 260631193766 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 521262387533) ^ 14088172636 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 521262387533) ^ 148 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_635536801589 : Nat.Prime 635536801589 := by
  apply lucas_primality 635536801589 (2 : ZMod 635536801589)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (31, 1), (2423, 1), (162713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (31, 1), (2423, 1), (162713, 1)] : List FactorBlock).map factorBlockValue).prod) = 635536801589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_2423
      · exact prime_twentyEightZ_162713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 635536801589) ^ 317768400794 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 635536801589) ^ 48887446276 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 635536801589) ^ 20501187148 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 635536801589) ^ 262293356 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 635536801589) ^ 3905876 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_780978274411 : Nat.Prime 780978274411 := by
  apply lucas_primality 780978274411 (2 : ZMod 780978274411)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (47, 1), (14969873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (47, 1), (14969873, 1)] : List FactorBlock).map factorBlockValue).prod) = 780978274411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_14969873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 780978274411) ^ 390489137205 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 780978274411) ^ 260326091470 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 780978274411) ^ 156195654882 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 780978274411) ^ 21107520930 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 780978274411) ^ 16616559030 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 780978274411) ^ 52170 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_852391097893 : Nat.Prime 852391097893 := by
  apply lucas_primality 852391097893 (2 : ZMod 852391097893)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (853, 1), (27757949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (853, 1), (27757949, 1)] : List FactorBlock).map factorBlockValue).prod) = 852391097893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_853
      · exact prime_twentyEightZ_27757949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 852391097893) ^ 426195548946 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 284130365964 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 999286164 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 30708 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_977519457737 : Nat.Prime 977519457737 := by
  apply lucas_primality 977519457737 (3 : ZMod 977519457737)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1259, 1), (3643, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1259, 1), (3643, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) = 977519457737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_1259
      · exact prime_twentyEightZ_3643
      · exact prime_twentyEightZ_26641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 977519457737) ^ 488759728868 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 776425304 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 268328152 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 36692296 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_999086680303 : Nat.Prime 999086680303 := by
  apply lucas_primality 999086680303 (5 : ZMod 999086680303)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (5741877473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (5741877473, 1)] : List FactorBlock).map factorBlockValue).prod) = 999086680303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_5741877473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 999086680303) ^ 499543340151 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 999086680303) ^ 333028893434 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 999086680303) ^ 34451264838 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 999086680303) ^ 174 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1026349089653 : Nat.Prime 1026349089653 := by
  apply lucas_primality 1026349089653 (2 : ZMod 1026349089653)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1223, 1), (209801531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1223, 1), (209801531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026349089653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_1223
      · exact prime_twentyEightZ_209801531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1026349089653) ^ 513174544826 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026349089653) ^ 839206124 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026349089653) ^ 4892 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1147292922091 : Nat.Prime 1147292922091 := by
  apply lucas_primality 1147292922091 (2 : ZMod 1147292922091)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (61, 1), (89562289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (61, 1), (89562289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1147292922091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_61
      · exact prime_twentyEightZ_89562289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1147292922091) ^ 573646461045 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1147292922091) ^ 382430974030 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1147292922091) ^ 229458584418 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1147292922091) ^ 163898988870 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1147292922091) ^ 18808080690 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1147292922091) ^ 12810 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1438921022293 : Nat.Prime 1438921022293 := by
  apply lucas_primality 1438921022293 (7 : ZMod 1438921022293)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (17, 1), (3109, 1), (19391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (17, 1), (3109, 1), (19391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1438921022293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_3109
      · exact prime_twentyEightZ_19391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1438921022293) ^ 719460511146 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1438921022293) ^ 479640340764 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1438921022293) ^ 110686232484 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1438921022293) ^ 84642413076 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1438921022293) ^ 462824388 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1438921022293) ^ 74205612 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_35279
      · exact prime_twentyEightZ_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2190694981879 : Nat.Prime 2190694981879 := by
  apply lucas_primality 2190694981879 (6 : ZMod 2190694981879)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (9361944367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (9361944367, 1)] : List FactorBlock).map factorBlockValue).prod) = 2190694981879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_9361944367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2190694981879) ^ 1095347490939 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2190694981879) ^ 730231660626 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2190694981879) ^ 168514998606 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2190694981879) ^ 234 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2192745608479 : Nat.Prime 2192745608479 := by
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod) = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_9739
      · exact prime_twentyEightZ_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2192745608479) ^ 1096372804239 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 730915202826 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 95336765586 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 225151002 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2192745608479) ^ 36287514 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2364941291179 : Nat.Prime 2364941291179 := by
  apply lucas_primality 2364941291179 (2 : ZMod 2364941291179)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (7331, 1), (1453129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (7331, 1), (1453129, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364941291179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_7331
      · exact prime_twentyEightZ_1453129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2364941291179) ^ 1182470645589 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364941291179) ^ 788313763726 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364941291179) ^ 63917332194 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364941291179) ^ 322594638 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2364941291179) ^ 1627482 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2391682846193 : Nat.Prime 2391682846193 := by
  apply lucas_primality 2391682846193 (3 : ZMod 2391682846193)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (47939, 1), (135571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (47939, 1), (135571, 1)] : List FactorBlock).map factorBlockValue).prod) = 2391682846193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_47939
      · exact prime_twentyEightZ_135571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2391682846193) ^ 1195841423096 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2391682846193) ^ 103986210704 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2391682846193) ^ 49890128 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2391682846193) ^ 17641552 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_4579925118581 : Nat.Prime 4579925118581 := by
  apply lucas_primality 4579925118581 (3 : ZMod 4579925118581)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (5741, 1), (5698267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (5741, 1), (5698267, 1)] : List FactorBlock).map factorBlockValue).prod) = 4579925118581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_5741
      · exact prime_twentyEightZ_5698267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4579925118581) ^ 2289962559290 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4579925118581) ^ 915985023716 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4579925118581) ^ 654275016940 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4579925118581) ^ 797757380 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4579925118581) ^ 803740 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_5548168639781 : Nat.Prime 5548168639781 := by
  apply lucas_primality 5548168639781 (2 : ZMod 5548168639781)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (11353, 1), (1879601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (11353, 1), (1879601, 1)] : List FactorBlock).map factorBlockValue).prod) = 5548168639781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_11353
      · exact prime_twentyEightZ_1879601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5548168639781) ^ 2774084319890 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5548168639781) ^ 1109633727956 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5548168639781) ^ 426782203060 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5548168639781) ^ 488696260 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5548168639781) ^ 2951780 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_7007144209529 : Nat.Prime 7007144209529 := by
  apply lucas_primality 7007144209529 (3 : ZMod 7007144209529)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (112573, 1), (7780667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (112573, 1), (7780667, 1)] : List FactorBlock).map factorBlockValue).prod) = 7007144209529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_112573
      · exact prime_twentyEightZ_7780667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7007144209529) ^ 3503572104764 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7007144209529) ^ 62245336 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7007144209529) ^ 900584 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_7412691492859 : Nat.Prime 7412691492859 := by
  apply lucas_primality 7412691492859 (2 : ZMod 7412691492859)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (2591, 1), (8081747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (2591, 1), (8081747, 1)] : List FactorBlock).map factorBlockValue).prod) = 7412691492859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_2591
      · exact prime_twentyEightZ_8081747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7412691492859) ^ 3706345746429 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7412691492859) ^ 2470897164286 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7412691492859) ^ 125638838862 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7412691492859) ^ 2860938438 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7412691492859) ^ 917214 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_9427522870043 : Nat.Prime 9427522870043 := by
  apply lucas_primality 9427522870043 (2 : ZMod 9427522870043)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (277280084413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (277280084413, 1)] : List FactorBlock).map factorBlockValue).prod) = 9427522870043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_277280084413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9427522870043) ^ 4713761435021 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9427522870043) ^ 554560168826 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9427522870043) ^ 34 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_13203689273969 : Nat.Prime 13203689273969 := by
  apply lucas_primality 13203689273969 (3 : ZMod 13203689273969)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) = 13203689273969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_971
      · exact prime_twentyEightZ_1031
      · exact prime_twentyEightZ_22279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13203689273969) ^ 6601844636984 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 356856466864 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 13598032208 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 12806682128 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 592651792 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_17198039427347 : Nat.Prime 17198039427347 := by
  apply lucas_primality 17198039427347 (2 : ZMod 17198039427347)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (941, 1), (1327, 1), (2281, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (941, 1), (1327, 1), (2281, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) = 17198039427347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_941
      · exact prime_twentyEightZ_1327
      · exact prime_twentyEightZ_2281
      · exact prime_twentyEightZ_3019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17198039427347) ^ 8599019713673 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17198039427347) ^ 18276343706 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17198039427347) ^ 12960089998 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17198039427347) ^ 7539692866 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 17198039427347) ^ 5696601334 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_17336896205039 : Nat.Prime 17336896205039 := by
  apply lucas_primality 17336896205039 (11 : ZMod 17336896205039)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (41082692429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (41082692429, 1)] : List FactorBlock).map factorBlockValue).prod) = 17336896205039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_211
      · exact prime_twentyEightZ_41082692429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 17336896205039) ^ 8668448102519 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 17336896205039) ^ 82165384858 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 17336896205039) ^ 422 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_17630858458781 : Nat.Prime 17630858458781 := by
  apply lucas_primality 17630858458781 (3 : ZMod 17630858458781)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (125934703277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (125934703277, 1)] : List FactorBlock).map factorBlockValue).prod) = 17630858458781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_125934703277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17630858458781) ^ 8815429229390 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17630858458781) ^ 3526171691756 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17630858458781) ^ 2518694065540 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17630858458781) ^ 140 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_20891925688057 : Nat.Prime 20891925688057 := by
  apply lucas_primality 20891925688057 (5 : ZMod 20891925688057)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4297, 1), (202582477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4297, 1), (202582477, 1)] : List FactorBlock).map factorBlockValue).prod) = 20891925688057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_4297
      · exact prime_twentyEightZ_202582477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20891925688057) ^ 10445962844028 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20891925688057) ^ 6963975229352 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20891925688057) ^ 4861979448 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20891925688057) ^ 103128 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_20987836212361 : Nat.Prime 20987836212361 := by
  apply lucas_primality 20987836212361 (13 : ZMod 20987836212361)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (103, 1), (1698045001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (103, 1), (1698045001, 1)] : List FactorBlock).map factorBlockValue).prod) = 20987836212361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_103
      · exact prime_twentyEightZ_1698045001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 20987836212361) ^ 10493918106180 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 20987836212361) ^ 6995945404120 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 20987836212361) ^ 4197567242472 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 20987836212361) ^ 203765400120 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 20987836212361) ^ 12360 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_21910764024983 : Nat.Prime 21910764024983 := by
  apply lucas_primality 21910764024983 (5 : ZMod 21910764024983)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) = 21910764024983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_97
      · exact prime_twentyEightZ_22951043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21910764024983) ^ 10955382012491 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 3130109146426 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 1153198106578 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 592182811486 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 225884165206 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 954674 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_22844225199353 : Nat.Prime 22844225199353 := by
  apply lucas_primality 22844225199353 (3 : ZMod 22844225199353)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (659, 1), (19249, 1), (225109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (659, 1), (19249, 1), (225109, 1)] : List FactorBlock).map factorBlockValue).prod) = 22844225199353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_659
      · exact prime_twentyEightZ_19249
      · exact prime_twentyEightZ_225109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22844225199353) ^ 11422112599676 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22844225199353) ^ 34664985128 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22844225199353) ^ 1186774648 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22844225199353) ^ 101480728 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_27346626158783 : Nat.Prime 27346626158783 := by
  apply lucas_primality 27346626158783 (5 : ZMod 27346626158783)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (84927410431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (84927410431, 1)] : List FactorBlock).map factorBlockValue).prod) = 27346626158783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_84927410431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27346626158783) ^ 13673313079391 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 3906660879826 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 1188983746034 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 322 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_36268517031751 : Nat.Prime 36268517031751 := by
  apply lucas_primality 36268517031751 (11 : ZMod 36268517031751)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (31079, 1), (518657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (31079, 1), (518657, 1)] : List FactorBlock).map factorBlockValue).prod) = 36268517031751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_31079
      · exact prime_twentyEightZ_518657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 36268517031751) ^ 18134258515875 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 36268517031751) ^ 12089505677250 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 36268517031751) ^ 7253703406350 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 36268517031751) ^ 1166978250 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 36268517031751) ^ 69927750 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_38554545693913 : Nat.Prime 38554545693913 := by
  apply lucas_primality 38554545693913 (10 : ZMod 38554545693913)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) = 38554545693913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_293
      · exact prime_twentyEightZ_317
      · exact prime_twentyEightZ_293147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 38554545693913) ^ 19277272846956 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 12851515231304 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 653466876168 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131585480184 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 121623172536 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131519496 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_39530687550041 : Nat.Prime 39530687550041 := by
  apply lucas_primality 39530687550041 (3 : ZMod 39530687550041)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) = 39530687550041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_101
      · exact prime_twentyEightZ_5779
      · exact prime_twentyEightZ_1693169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39530687550041) ^ 19765343775020 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 7906137510008 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 391392946040 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 6840402760 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 23347160 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_41007301887107 : Nat.Prime 41007301887107 := by
  apply lucas_primality 41007301887107 (2 : ZMod 41007301887107)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) = 41007301887107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_601
      · exact prime_twentyEightZ_1069
      · exact prime_twentyEightZ_31913837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41007301887107) ^ 20503650943553 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 68231783506 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 38360432074 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 1284938 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_46558229274047 : Nat.Prime 46558229274047 := by
  apply lucas_primality 46558229274047 (7 : ZMod 46558229274047)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (151939, 1), (951637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (151939, 1), (951637, 1)] : List FactorBlock).map factorBlockValue).prod) = 46558229274047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_151939
      · exact prime_twentyEightZ_951637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 46558229274047) ^ 23279114637023 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 6651175610578 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 2024270838002 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 306427114 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 48924358 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_60421700572451 : Nat.Prime 60421700572451 := by
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod) = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_89
      · exact prime_twentyEightZ_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60421700572451) ^ 30210850286225 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 12084340114490 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 8631671510350 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 678895512050 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 60421700572451) ^ 218050 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_70210231615351 : Nat.Prime 70210231615351 := by
  apply lucas_primality 70210231615351 (3 : ZMod 70210231615351)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (1733, 1), (90030431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (1733, 1), (90030431, 1)] : List FactorBlock).map factorBlockValue).prod) = 70210231615351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_1733
      · exact prime_twentyEightZ_90030431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70210231615351) ^ 35105115807675 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 70210231615351) ^ 23403410538450 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 70210231615351) ^ 14042046323070 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 70210231615351) ^ 40513693950 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 70210231615351) ^ 779850 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_90451742869699 : Nat.Prime 90451742869699 := by
  apply lucas_primality 90451742869699 (2 : ZMod 90451742869699)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (59, 1), (36501913991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (59, 1), (36501913991, 1)] : List FactorBlock).map factorBlockValue).prod) = 90451742869699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_36501913991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90451742869699) ^ 45225871434849 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 90451742869699) ^ 30150580956566 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 90451742869699) ^ 12921677552814 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 90451742869699) ^ 1533080387622 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 90451742869699) ^ 2478 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_122160859692467 : Nat.Prime 122160859692467 := by
  apply lucas_primality 122160859692467 (2 : ZMod 122160859692467)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (271, 1), (379, 1), (12136613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (271, 1), (379, 1), (12136613, 1)] : List FactorBlock).map factorBlockValue).prod) = 122160859692467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_271
      · exact prime_twentyEightZ_379
      · exact prime_twentyEightZ_12136613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122160859692467) ^ 61080429846233 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 122160859692467) ^ 17451551384638 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 122160859692467) ^ 450778080046 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 122160859692467) ^ 322324168054 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 122160859692467) ^ 10065482 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_135096519595393 : Nat.Prime 135096519595393 := by
  apply lucas_primality 135096519595393 (10 : ZMod 135096519595393)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (275491, 1), (425681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (275491, 1), (425681, 1)] : List FactorBlock).map factorBlockValue).prod) = 135096519595393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_275491
      · exact prime_twentyEightZ_425681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 135096519595393) ^ 67548259797696 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 45032173198464 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 490384512 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 317365632 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_159837705232951 : Nat.Prime 159837705232951 := by
  apply lucas_primality 159837705232951 (3 : ZMod 159837705232951)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (43, 1), (131, 1), (189168241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (43, 1), (131, 1), (189168241, 1)] : List FactorBlock).map factorBlockValue).prod) = 159837705232951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_131
      · exact prime_twentyEightZ_189168241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 159837705232951) ^ 79918852616475 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 159837705232951) ^ 53279235077650 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 159837705232951) ^ 31967541046590 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 159837705232951) ^ 3717155935650 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 159837705232951) ^ 1220135154450 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 159837705232951) ^ 844950 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_270982644017201 : Nat.Prime 270982644017201 := by
  apply lucas_primality 270982644017201 (3 : ZMod 270982644017201)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (33347, 1), (20315369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (33347, 1), (20315369, 1)] : List FactorBlock).map factorBlockValue).prod) = 270982644017201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_33347
      · exact prime_twentyEightZ_20315369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 270982644017201) ^ 135491322008600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 270982644017201) ^ 54196528803440 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 270982644017201) ^ 8126147600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 270982644017201) ^ 13338800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_324019525513781 : Nat.Prime 324019525513781 := by
  apply lucas_primality 324019525513781 (2 : ZMod 324019525513781)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (344701622887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (344701622887, 1)] : List FactorBlock).map factorBlockValue).prod) = 324019525513781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_344701622887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 324019525513781) ^ 162009762756890 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 324019525513781) ^ 64803905102756 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 324019525513781) ^ 6894032457740 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 324019525513781) ^ 940 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_376537177183483 : Nat.Prime 376537177183483 := by
  apply lucas_primality 376537177183483 (2 : ZMod 376537177183483)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (7, 4), (35853943, 1)] : List FactorBlock).map factorBlockValue).prod) = 376537177183483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_35853943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376537177183483) ^ 188268588591741 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 125512392394494 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 53791025311926 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 376537177183483) ^ 10501974 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_415034571917257 : Nat.Prime 415034571917257 := by
  apply lucas_primality 415034571917257 (5 : ZMod 415034571917257)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (59, 1), (13331, 1), (758159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (59, 1), (13331, 1), (758159, 1)] : List FactorBlock).map factorBlockValue).prod) = 415034571917257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_13331
      · exact prime_twentyEightZ_758159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 415034571917257) ^ 207517285958628 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 138344857305752 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 14311536962664 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 7034484269784 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 31133041176 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 547424184 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_460793340036793 : Nat.Prime 460793340036793 := by
  apply lucas_primality 460793340036793 (10 : ZMod 460793340036793)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (19, 1), (641, 1), (1049, 1), (71563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (19, 1), (641, 1), (1049, 1), (71563, 1)] : List FactorBlock).map factorBlockValue).prod) = 460793340036793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_641
      · exact prime_twentyEightZ_1049
      · exact prime_twentyEightZ_71563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 460793340036793) ^ 230396670018396 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 460793340036793) ^ 153597780012264 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 460793340036793) ^ 65827620005256 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 460793340036793) ^ 24252281054568 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 460793340036793) ^ 718866365112 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 460793340036793) ^ 439269151608 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 460793340036793) ^ 6438988584 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_491413453268053 : Nat.Prime 491413453268053 := by
  apply lucas_primality 491413453268053 (5 : ZMod 491413453268053)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (71, 1), (151, 1), (545672993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (71, 1), (151, 1), (545672993, 1)] : List FactorBlock).map factorBlockValue).prod) = 491413453268053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_71
      · exact prime_twentyEightZ_151
      · exact prime_twentyEightZ_545672993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 491413453268053) ^ 245706726634026 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 491413453268053) ^ 163804484422684 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 491413453268053) ^ 70201921895436 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 491413453268053) ^ 6921316243212 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 491413453268053) ^ 3254393730252 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 491413453268053) ^ 900564 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_598744972004371 : Nat.Prime 598744972004371 := by
  apply lucas_primality 598744972004371 (2 : ZMod 598744972004371)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) = 598744972004371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_107
      · exact prime_twentyEightZ_233
      · exact prime_twentyEightZ_409
      · exact prime_twentyEightZ_1957301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598744972004371) ^ 299372486002185 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 199581657334790 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 119748994400874 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 5595747401910 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 2569720909890 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 1463924136930 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 305903370 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_621911721757133 : Nat.Prime 621911721757133 := by
  apply lucas_primality 621911721757133 (2 : ZMod 621911721757133)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1123, 1), (138448735921, 1)] : List FactorBlock).map factorBlockValue).prod) = 621911721757133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_1123
      · exact prime_twentyEightZ_138448735921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621911721757133) ^ 310955860878566 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 553794943684 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 621911721757133) ^ 4492 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_659702079143411 : Nat.Prime 659702079143411 := by
  apply lucas_primality 659702079143411 (2 : ZMod 659702079143411)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (230291, 1), (286464551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (230291, 1), (286464551, 1)] : List FactorBlock).map factorBlockValue).prod) = 659702079143411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_230291
      · exact prime_twentyEightZ_286464551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 659702079143411) ^ 329851039571705 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 131940415828682 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 2864645510 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 2302910 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_806066820870257 : Nat.Prime 806066820870257 := by
  apply lucas_primality 806066820870257 (3 : ZMod 806066820870257)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (4579925118581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (4579925118581, 1)] : List FactorBlock).map factorBlockValue).prod) = 806066820870257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_4579925118581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 806066820870257) ^ 403033410435128 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 806066820870257) ^ 73278801897296 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 806066820870257) ^ 176 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_817016986973969 : Nat.Prime 817016986973969 := by
  apply lucas_primality 817016986973969 (3 : ZMod 817016986973969)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) = 817016986973969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_223
      · exact prime_twentyEightZ_283
      · exact prime_twentyEightZ_5843
      · exact prime_twentyEightZ_12589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817016986973969) ^ 408508493486984 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 74274271543088 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 3663753304816 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 2886985819696 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 139828339376 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 64899276112 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1217879459003443 : Nat.Prime 1217879459003443 := by
  apply lucas_primality 1217879459003443 (2 : ZMod 1217879459003443)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (7817, 1), (1366656409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (7817, 1), (1366656409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1217879459003443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_7817
      · exact prime_twentyEightZ_1366656409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1217879459003443) ^ 608939729501721 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217879459003443) ^ 405959819667814 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217879459003443) ^ 64098918894918 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217879459003443) ^ 155798830626 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217879459003443) ^ 891138 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1583581521533941 : Nat.Prime 1583581521533941 := by
  apply lucas_primality 1583581521533941 (2 : ZMod 1583581521533941)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (977519457737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (977519457737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1583581521533941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_977519457737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1583581521533941) ^ 791790760766970 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 527860507177980 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 316716304306788 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 1620 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2224710638510267 : Nat.Prime 2224710638510267 := by
  apply lucas_primality 2224710638510267 (2 : ZMod 2224710638510267)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (20987836212361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (20987836212361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2224710638510267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_20987836212361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2224710638510267) ^ 1112355319255133 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224710638510267) ^ 41975672424722 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2224710638510267) ^ 106 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_6933661561302821 : Nat.Prime 6933661561302821 := by
  apply lucas_primality 6933661561302821 (2 : ZMod 6933661561302821)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (347, 1), (999086680303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (347, 1), (999086680303, 1)] : List FactorBlock).map factorBlockValue).prod) = 6933661561302821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_347
      · exact prime_twentyEightZ_999086680303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6933661561302821) ^ 3466830780651410 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6933661561302821) ^ 1386732312260564 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6933661561302821) ^ 19981733606060 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6933661561302821) ^ 6940 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_7797332648072969 : Nat.Prime 7797332648072969 := by
  apply lucas_primality 7797332648072969 (3 : ZMod 7797332648072969)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (13, 1), (197, 1), (4942603493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (13, 1), (197, 1), (4942603493, 1)] : List FactorBlock).map factorBlockValue).prod) = 7797332648072969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_197
      · exact prime_twentyEightZ_4942603493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7797332648072969) ^ 3898666324036484 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7797332648072969) ^ 1113904664010424 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7797332648072969) ^ 708848422552088 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7797332648072969) ^ 599794819082536 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7797332648072969) ^ 39580368771944 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7797332648072969) ^ 1577576 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_8145863230900253 : Nat.Prime 8145863230900253 := by
  apply lucas_primality 8145863230900253 (2 : ZMod 8145863230900253)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (28759, 1), (495184799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (28759, 1), (495184799, 1)] : List FactorBlock).map factorBlockValue).prod) = 8145863230900253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_28759
      · exact prime_twentyEightZ_495184799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8145863230900253) ^ 4072931615450126 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8145863230900253) ^ 740533020990932 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8145863230900253) ^ 626604863915404 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8145863230900253) ^ 283245705028 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8145863230900253) ^ 16450148 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_8438917837893001 : Nat.Prime 8438917837893001 := by
  apply lucas_primality 8438917837893001 (11 : ZMod 8438917837893001)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (59, 1), (40433, 1), (1179173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (59, 1), (40433, 1), (1179173, 1)] : List FactorBlock).map factorBlockValue).prod) = 8438917837893001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_40433
      · exact prime_twentyEightZ_1179173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8438917837893001) ^ 4219458918946500 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 2812972612631000 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 1687783567578600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 143032505727000 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 208713621000 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (11 : ZMod 8438917837893001) ^ 7156641000 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_13608820071578803 : Nat.Prime 13608820071578803 := by
  apply lucas_primality 13608820071578803 (3 : ZMod 13608820071578803)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (324019525513781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (324019525513781, 1)] : List FactorBlock).map factorBlockValue).prod) = 13608820071578803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_324019525513781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13608820071578803) ^ 6804410035789401 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13608820071578803) ^ 4536273357192934 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13608820071578803) ^ 1944117153082686 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13608820071578803) ^ 42 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_16877197084131511 : Nat.Prime 16877197084131511 := by
  apply lucas_primality 16877197084131511 (6 : ZMod 16877197084131511)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (53, 1), (89, 1), (17037864143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (53, 1), (89, 1), (17037864143, 1)] : List FactorBlock).map factorBlockValue).prod) = 16877197084131511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_89
      · exact prime_twentyEightZ_17037864143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16877197084131511) ^ 8438598542065755 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 5625732361377170 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 3375439416826302 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 2411028154875930 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 318437680832670 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 189631427911590 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 990570 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_17797685108082137 : Nat.Prime 17797685108082137 := by
  apply lucas_primality 17797685108082137 (3 : ZMod 17797685108082137)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2224710638510267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2224710638510267, 1)] : List FactorBlock).map factorBlockValue).prod) = 17797685108082137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_2224710638510267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 17797685108082137) ^ 8898842554041068 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17797685108082137) ^ 8 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_20000838920189041 : Nat.Prime 20000838920189041 := by
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_384973
      · exact prime_twentyEightZ_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20000838920189041) ^ 10000419460094520 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 6666946306729680 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 4000167784037808 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 51953874480 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 20000838920189041) ^ 277180560 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_20634127459681621 : Nat.Prime 20634127459681621 := by
  apply lucas_primality 20634127459681621 (2 : ZMod 20634127459681621)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (239, 1), (1438921022293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (239, 1), (1438921022293, 1)] : List FactorBlock).map factorBlockValue).prod) = 20634127459681621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_239
      · exact prime_twentyEightZ_1438921022293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20634127459681621) ^ 10317063729840810 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20634127459681621) ^ 6878042486560540 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20634127459681621) ^ 4126825491936324 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20634127459681621) ^ 86335261337580 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20634127459681621) ^ 14340 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_20660407174714891 : Nat.Prime 20660407174714891 := by
  apply lucas_primality 20660407174714891 (2 : ZMod 20660407174714891)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (1026349089653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (1026349089653, 1)] : List FactorBlock).map factorBlockValue).prod) = 20660407174714891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_61
      · exact prime_twentyEightZ_1026349089653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20660407174714891) ^ 10330203587357445 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 6886802391571630 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 4132081434942978 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 1878218834064990 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 338695199585490 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 20130 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_21292507748726713 : Nat.Prime 21292507748726713 := by
  apply lucas_primality 21292507748726713 (5 : ZMod 21292507748726713)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (241, 1), (93199, 1), (13166369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (241, 1), (93199, 1), (13166369, 1)] : List FactorBlock).map factorBlockValue).prod) = 21292507748726713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_241
      · exact prime_twentyEightZ_93199
      · exact prime_twentyEightZ_13166369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21292507748726713) ^ 10646253874363356 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21292507748726713) ^ 7097502582908904 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21292507748726713) ^ 88350654559032 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21292507748726713) ^ 228462834888 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21292507748726713) ^ 1617189048 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_22145781469408963 : Nat.Prime 22145781469408963 := by
  apply lucas_primality 22145781469408963 (2 : ZMod 22145781469408963)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod) = 22145781469408963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_89
      · exact prime_twentyEightZ_163
      · exact prime_twentyEightZ_254426385761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22145781469408963) ^ 11072890734704481 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 7381927156469654 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 248829005274258 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 135863689996374 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 87042 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_22624945031209403 : Nat.Prime 22624945031209403 := by
  apply lucas_primality 22624945031209403 (2 : ZMod 22624945031209403)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (17, 1), (163003, 1), (83313799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (17, 1), (163003, 1), (83313799, 1)] : List FactorBlock).map factorBlockValue).prod) = 22624945031209403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_163003
      · exact prime_twentyEightZ_83313799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22624945031209403) ^ 11312472515604701 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 22624945031209403) ^ 3232135004458486 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 22624945031209403) ^ 1330879119482906 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 22624945031209403) ^ 138800789134 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 22624945031209403) ^ 271562998 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_26110404665159999 : Nat.Prime 26110404665159999 := by
  apply lucas_primality 26110404665159999 (7 : ZMod 26110404665159999)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (727369, 1), (17948527271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (727369, 1), (17948527271, 1)] : List FactorBlock).map factorBlockValue).prod) = 26110404665159999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_727369
      · exact prime_twentyEightZ_17948527271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 26110404665159999) ^ 13055202332579999 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 26110404665159999) ^ 35897054542 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 26110404665159999) ^ 1454738 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_35912884381670059 : Nat.Prime 35912884381670059 := by
  apply lucas_primality 35912884381670059 (10 : ZMod 35912884381670059)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (19, 1), (15319, 1), (172809677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (19, 1), (15319, 1), (172809677, 1)] : List FactorBlock).map factorBlockValue).prod) = 35912884381670059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_15319
      · exact prime_twentyEightZ_172809677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 35912884381670059) ^ 17956442190835029 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 35912884381670059) ^ 11970961460556686 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 35912884381670059) ^ 5130412054524294 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 35912884381670059) ^ 2112522610686474 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 35912884381670059) ^ 1890151809561582 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 35912884381670059) ^ 2344336078182 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 35912884381670059) ^ 207817554 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_56909605574267269 : Nat.Prime 56909605574267269 := by
  apply lucas_primality 56909605574267269 (2 : ZMod 56909605574267269)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (227, 1), (20891925688057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (227, 1), (20891925688057, 1)] : List FactorBlock).map factorBlockValue).prod) = 56909605574267269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_227
      · exact prime_twentyEightZ_20891925688057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56909605574267269) ^ 28454802787133634 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56909605574267269) ^ 18969868524755756 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56909605574267269) ^ 250703108256684 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56909605574267269) ^ 2724 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_63506352168529163 : Nat.Prime 63506352168529163 := by
  apply lucas_primality 63506352168529163 (2 : ZMod 63506352168529163)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1801, 1), (17630858458781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1801, 1), (17630858458781, 1)] : List FactorBlock).map factorBlockValue).prod) = 63506352168529163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_1801
      · exact prime_twentyEightZ_17630858458781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63506352168529163) ^ 31753176084264581 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 63506352168529163) ^ 35261716917562 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 63506352168529163) ^ 3602 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_97937826197793863 : Nat.Prime 97937826197793863 := by
  apply lucas_primality 97937826197793863 (5 : ZMod 97937826197793863)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (167, 1), (316097, 1), (1489003, 1)] : List FactorBlock).map factorBlockValue).prod) = 97937826197793863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_89
      · exact prime_twentyEightZ_167
      · exact prime_twentyEightZ_316097
      · exact prime_twentyEightZ_1489003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97937826197793863) ^ 48968913098896931 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 13991118028256266 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 1100425013458358 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 586454049088586 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 309834722246 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 97937826197793863) ^ 65774095954 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_114218290024018991 : Nat.Prime 114218290024018991 := by
  apply lucas_primality 114218290024018991 (17 : ZMod 114218290024018991)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (491, 1), (2677, 1), (15073, 1), (576509, 1)] : List FactorBlock).map factorBlockValue).prod) = 114218290024018991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_491
      · exact prime_twentyEightZ_2677
      · exact prime_twentyEightZ_15073
      · exact prime_twentyEightZ_576509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 114218290024018991) ^ 57109145012009495 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 22843658004803798 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 232623808602890 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 42666525970870 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 7577674651630 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (17 : ZMod 114218290024018991) ^ 198120567110 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_158361893331124207 : Nat.Prime 158361893331124207 := by
  apply lucas_primality 158361893331124207 (5 : ZMod 158361893331124207)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (10049639, 1), (27075547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (10049639, 1), (27075547, 1)] : List FactorBlock).map factorBlockValue).prod) = 158361893331124207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_97
      · exact prime_twentyEightZ_10049639
      · exact prime_twentyEightZ_27075547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 158361893331124207) ^ 79180946665562103 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 52787297777041402 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 1632596838465198 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 15757968354 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 5848889898 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_180018837229260329 : Nat.Prime 180018837229260329 := by
  apply lucas_primality 180018837229260329 (3 : ZMod 180018837229260329)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) = 180018837229260329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_79
      · exact prime_twentyEightZ_21910764024983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180018837229260329) ^ 90009418614630164 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 13847602863789256 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 2278719458598232 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 8216 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_195766863462661819 : Nat.Prime 195766863462661819 := by
  apply lucas_primality 195766863462661819 (3 : ZMod 195766863462661819)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (10601, 1), (133817607761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (10601, 1), (133817607761, 1)] : List FactorBlock).map factorBlockValue).prod) = 195766863462661819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_10601
      · exact prime_twentyEightZ_133817607761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 195766863462661819) ^ 97883431731330909 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 195766863462661819) ^ 65255621154220606 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 195766863462661819) ^ 8511602759246166 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 195766863462661819) ^ 18466829871018 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 195766863462661819) ^ 1462938 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_248268580828039157 : Nat.Prime 248268580828039157 := by
  apply lucas_primality 248268580828039157 (2 : ZMod 248268580828039157)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (806066820870257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (806066820870257, 1)] : List FactorBlock).map factorBlockValue).prod) = 248268580828039157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_806066820870257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 248268580828039157) ^ 124134290414019578 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 248268580828039157) ^ 35466940118291308 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 248268580828039157) ^ 22569870984367196 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 248268580828039157) ^ 308 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_381772691531587337 : Nat.Prime 381772691531587337 := by
  apply lucas_primality 381772691531587337 (3 : ZMod 381772691531587337)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2089, 1), (22844225199353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2089, 1), (22844225199353, 1)] : List FactorBlock).map factorBlockValue).prod) = 381772691531587337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_2089
      · exact prime_twentyEightZ_22844225199353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 381772691531587337) ^ 190886345765793668 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 381772691531587337) ^ 182753801594824 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 381772691531587337) ^ 16712 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_61717
      · exact prime_twentyEightZ_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1236495880396527397 : Nat.Prime 1236495880396527397 := by
  apply lucas_primality 1236495880396527397 (2 : ZMod 1236495880396527397)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3307, 1), (116443, 1), (267586283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3307, 1), (116443, 1), (267586283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1236495880396527397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_3307
      · exact prime_twentyEightZ_116443
      · exact prime_twentyEightZ_267586283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1236495880396527397) ^ 618247940198263698 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236495880396527397) ^ 412165293465509132 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236495880396527397) ^ 373902594616428 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236495880396527397) ^ 10618894054572 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1236495880396527397) ^ 4620924012 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1570470015063981253 : Nat.Prime 1570470015063981253 := by
  apply lucas_primality 1570470015063981253 (5 : ZMod 1570470015063981253)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (89, 1), (1151, 1), (3301, 1), (2290081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (89, 1), (1151, 1), (3301, 1), (2290081, 1)] : List FactorBlock).map factorBlockValue).prod) = 1570470015063981253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_89
      · exact prime_twentyEightZ_1151
      · exact prime_twentyEightZ_3301
      · exact prime_twentyEightZ_2290081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1570470015063981253) ^ 785235007531990626 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 523490005021327084 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 120805385774152404 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 17645730506336868 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 1364439630811452 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 475755836129652 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 685770509892 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3357640771913012023 : Nat.Prime 3357640771913012023 := by
  apply lucas_primality 3357640771913012023 (5 : ZMod 3357640771913012023)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (439, 1), (20549, 1), (1088310731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (439, 1), (20549, 1), (1088310731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3357640771913012023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_439
      · exact prime_twentyEightZ_20549
      · exact prime_twentyEightZ_1088310731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3357640771913012023) ^ 1678820385956506011 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 1119213590637670674 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 176717935363842738 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 7648384446271098 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 163396796530878 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 3085185762 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3523803542327912743 : Nat.Prime 3523803542327912743 := by
  apply lucas_primality 3523803542327912743 (7 : ZMod 3523803542327912743)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (195766863462661819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (195766863462661819, 1)] : List FactorBlock).map factorBlockValue).prod) = 3523803542327912743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_195766863462661819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3523803542327912743) ^ 1761901771163956371 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3523803542327912743) ^ 1174601180775970914 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3523803542327912743) ^ 18 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_6055427446181247143 : Nat.Prime 6055427446181247143 := by
  apply lucas_primality 6055427446181247143 (5 : ZMod 6055427446181247143)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (55663, 1), (2364941291179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (55663, 1), (2364941291179, 1)] : List FactorBlock).map factorBlockValue).prod) = 6055427446181247143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_55663
      · exact prime_twentyEightZ_2364941291179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6055427446181247143) ^ 3027713723090623571 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6055427446181247143) ^ 263279454181793354 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6055427446181247143) ^ 108787299394234 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6055427446181247143) ^ 2560498 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_6446905430873149531 : Nat.Prime 6446905430873149531 := by
  apply lucas_primality 6446905430873149531 (3 : ZMod 6446905430873149531)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (673, 1), (26449, 1), (4024245521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (673, 1), (26449, 1), (4024245521, 1)] : List FactorBlock).map factorBlockValue).prod) = 6446905430873149531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_673
      · exact prime_twentyEightZ_26449
      · exact prime_twentyEightZ_4024245521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6446905430873149531) ^ 3223452715436574765 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6446905430873149531) ^ 2148968476957716510 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6446905430873149531) ^ 1289381086174629906 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6446905430873149531) ^ 9579354280643610 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6446905430873149531) ^ 243748551206970 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6446905430873149531) ^ 1602015930 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_6901868647270889023 : Nat.Prime 6901868647270889023 := by
  apply lucas_primality 6901868647270889023 (3 : ZMod 6901868647270889023)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (227, 1), (1093, 1), (201577281629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (227, 1), (1093, 1), (201577281629, 1)] : List FactorBlock).map factorBlockValue).prod) = 6901868647270889023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_227
      · exact prime_twentyEightZ_1093
      · exact prime_twentyEightZ_201577281629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6901868647270889023) ^ 3450934323635444511 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6901868647270889023) ^ 2300622882423629674 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6901868647270889023) ^ 300081245533516914 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6901868647270889023) ^ 30404707697228586 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6901868647270889023) ^ 6314609924310054 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6901868647270889023) ^ 34239318 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_7361524796742341989 : Nat.Prime 7361524796742341989 := by
  apply lucas_primality 7361524796742341989 (2 : ZMod 7361524796742341989)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 1), (18223631, 1), (90735599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 1), (18223631, 1), (90735599, 1)] : List FactorBlock).map factorBlockValue).prod) = 7361524796742341989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_18223631
      · exact prime_twentyEightZ_90735599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7361524796742341989) ^ 3680762398371170994 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 2453841598914113996 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 1051646399534620284 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 138896694278157396 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 403954886748 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7361524796742341989) ^ 81131605212 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_439
      · exact prime_twentyEightZ_853
      · exact prime_twentyEightZ_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_11891227458126031349 : Nat.Prime 11891227458126031349 := by
  apply lucas_primality 11891227458126031349 (2 : ZMod 11891227458126031349)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (25457, 1), (852391097893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (25457, 1), (852391097893, 1)] : List FactorBlock).map factorBlockValue).prod) = 11891227458126031349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_137
      · exact prime_twentyEightZ_25457
      · exact prime_twentyEightZ_852391097893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11891227458126031349) ^ 5945613729063015674 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 86797280716248404 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 467110321645364 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 13950436 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_14143091156502206219 : Nat.Prime 14143091156502206219 := by
  apply lucas_primality 14143091156502206219 (2 : ZMod 14143091156502206219)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (419, 1), (16877197084131511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (419, 1), (16877197084131511, 1)] : List FactorBlock).map factorBlockValue).prod) = 14143091156502206219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_419
      · exact prime_twentyEightZ_16877197084131511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14143091156502206219) ^ 7071545578251103109 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14143091156502206219) ^ 33754394168263022 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14143091156502206219) ^ 838 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_19106783380496639413 : Nat.Prime 19106783380496639413 := by
  apply lucas_primality 19106783380496639413 (2 : ZMod 19106783380496639413)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (13608820071578803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (13608820071578803, 1)] : List FactorBlock).map factorBlockValue).prod) = 19106783380496639413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_13608820071578803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19106783380496639413) ^ 9553391690248319706 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19106783380496639413) ^ 6368927793498879804 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19106783380496639413) ^ 1469752567730510724 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19106783380496639413) ^ 1404 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_44183162164402972273 : Nat.Prime 44183162164402972273 := by
  apply lucas_primality 44183162164402972273 (5 : ZMod 44183162164402972273)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (113, 1), (8145863230900253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (113, 1), (8145863230900253, 1)] : List FactorBlock).map factorBlockValue).prod) = 44183162164402972273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_113
      · exact prime_twentyEightZ_8145863230900253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44183162164402972273) ^ 22091581082201486136 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44183162164402972273) ^ 14727720721467657424 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44183162164402972273) ^ 391001435083212144 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44183162164402972273) ^ 5424 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_93639150386551147643 : Nat.Prime 93639150386551147643 := by
  apply lucas_primality 93639150386551147643 (2 : ZMod 93639150386551147643)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) = 93639150386551147643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_139
      · exact prime_twentyEightZ_413869
      · exact prime_twentyEightZ_73987284121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93639150386551147643) ^ 46819575193275573821 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 8512650035141013422 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 673662952421231278 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 226253114842018 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 1265611402 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_151778658601724464337 : Nat.Prime 151778658601724464337 := by
  apply lucas_primality 151778658601724464337 (3 : ZMod 151778658601724464337)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (41, 1), (17797685108082137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (41, 1), (17797685108082137, 1)] : List FactorBlock).map factorBlockValue).prod) = 151778658601724464337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_17797685108082137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 151778658601724464337) ^ 75889329300862232168 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 151778658601724464337) ^ 11675281430901881872 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 151778658601724464337) ^ 3701918502481084496 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 151778658601724464337) ^ 8528 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_198003276191030887067 : Nat.Prime 198003276191030887067 := by
  apply lucas_primality 198003276191030887067 (2 : ZMod 198003276191030887067)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14143091156502206219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14143091156502206219, 1)] : List FactorBlock).map factorBlockValue).prod) = 198003276191030887067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_14143091156502206219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 198003276191030887067) ^ 99001638095515443533 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 198003276191030887067) ^ 28286182313004412438 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 198003276191030887067) ^ 14 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_361586454322254942197 : Nat.Prime 361586454322254942197 := by
  apply lucas_primality 361586454322254942197 (2 : ZMod 361586454322254942197)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (71, 1), (97937826197793863, 1)] : List FactorBlock).map factorBlockValue).prod) = 361586454322254942197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_71
      · exact prime_twentyEightZ_97937826197793863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361586454322254942197) ^ 180793227161127471098 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 27814342640173457092 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 5092766962285280876 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 361586454322254942197) ^ 3692 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_432565763252833233799 : Nat.Prime 432565763252833233799 := by
  apply lucas_primality 432565763252833233799 (3 : ZMod 432565763252833233799)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (503, 1), (1259, 1), (5527, 1), (20597651827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (503, 1), (1259, 1), (5527, 1), (20597651827, 1)] : List FactorBlock).map factorBlockValue).prod) = 432565763252833233799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_503
      · exact prime_twentyEightZ_1259
      · exact prime_twentyEightZ_5527
      · exact prime_twentyEightZ_20597651827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 432565763252833233799) ^ 216282881626416616899 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 432565763252833233799) ^ 144188587750944411266 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 432565763252833233799) ^ 859971696327700266 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 432565763252833233799) ^ 343578842933147922 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 432565763252833233799) ^ 78264114936282474 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 432565763252833233799) ^ 21000731874 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_607348163015529886877 : Nat.Prime 607348163015529886877 := by
  apply lucas_primality 607348163015529886877 (2 : ZMod 607348163015529886877)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2837, 1), (2633923, 1), (20319607769, 1)] : List FactorBlock).map factorBlockValue).prod) = 607348163015529886877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_2837
      · exact prime_twentyEightZ_2633923
      · exact prime_twentyEightZ_20319607769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 607348163015529886877) ^ 303674081507764943438 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 214081129014991148 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 230586908962612 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 607348163015529886877) ^ 29889758204 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_767070978526931087231 : Nat.Prime 767070978526931087231 := by
  apply lucas_primality 767070978526931087231 (38 : ZMod 767070978526931087231)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (23, 1), (37, 1), (6933661561302821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (23, 1), (37, 1), (6933661561302821, 1)] : List FactorBlock).map factorBlockValue).prod) = 767070978526931087231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_6933661561302821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 767070978526931087231) ^ 383535489263465543615 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 153414195705386217446 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 59005459886687006710 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 33350912109866569010 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 20731648068295434790 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (38 : ZMod 767070978526931087231) ^ 110630 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_927515741733830445223 : Nat.Prime 927515741733830445223 := by
  apply lucas_primality 927515741733830445223 (3 : ZMod 927515741733830445223)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (11891227458126031349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (11891227458126031349, 1)] : List FactorBlock).map factorBlockValue).prod) = 927515741733830445223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_11891227458126031349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 927515741733830445223) ^ 463757870866915222611 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 309171913911276815074 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 71347364748756188094 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 78 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_107
      · exact prime_twentyEightZ_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2363845045067156754137 : Nat.Prime 2363845045067156754137 := by
  apply lucas_primality 2363845045067156754137 (5 : ZMod 2363845045067156754137)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (17, 1), (37, 1), (37223, 1), (1147292922091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (17, 1), (37, 1), (37223, 1), (1147292922091, 1)] : List FactorBlock).map factorBlockValue).prod) = 2363845045067156754137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_37223
      · exact prime_twentyEightZ_1147292922091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2363845045067156754137) ^ 1181922522533578377068 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2363845045067156754137) ^ 214895004097014250376 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2363845045067156754137) ^ 139049708533362162008 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2363845045067156754137) ^ 63887703920733966328 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2363845045067156754137) ^ 63504957823581032 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2363845045067156754137) ^ 2060367496 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2549893347446836525949 : Nat.Prime 2549893347446836525949 := by
  apply lucas_primality 2549893347446836525949 (2 : ZMod 2549893347446836525949)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (580732433, 1), (5252180671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (580732433, 1), (5252180671, 1)] : List FactorBlock).map factorBlockValue).prod) = 2549893347446836525949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_580732433
      · exact prime_twentyEightZ_5252180671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2549893347446836525949) ^ 1274946673723418262974 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2549893347446836525949) ^ 231808486131530593268 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2549893347446836525949) ^ 134204913023517711892 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2549893347446836525949) ^ 4390823040956 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2549893347446836525949) ^ 485492313988 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_2925172547624193772291 : Nat.Prime 2925172547624193772291 := by
  apply lucas_primality 2925172547624193772291 (2 : ZMod 2925172547624193772291)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 2), (20749, 1), (5548168639781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 2), (20749, 1), (5548168639781, 1)] : List FactorBlock).map factorBlockValue).prod) = 2925172547624193772291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_20749
      · exact prime_twentyEightZ_5548168639781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2925172547624193772291) ^ 1462586273812096886145 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2925172547624193772291) ^ 975057515874731257430 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2925172547624193772291) ^ 585034509524838754458 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2925172547624193772291) ^ 417881792517741967470 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2925172547624193772291) ^ 265924777056744888390 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2925172547624193772291) ^ 140978965136835210 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2925172547624193772291) ^ 527232090 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3376719396603664660873 : Nat.Prime 3376719396603664660873 := by
  apply lucas_primality 3376719396603664660873 (15 : ZMod 3376719396603664660873)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (2633, 1), (659702079143411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (2633, 1), (659702079143411, 1)] : List FactorBlock).map factorBlockValue).prod) = 3376719396603664660873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_2633
      · exact prime_twentyEightZ_659702079143411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 3376719396603664660873) ^ 1688359698301832330436 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 1125573132201221553624 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 1282460841854790984 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 5118552 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3463701263446490329787 : Nat.Prime 3463701263446490329787 := by
  apply lucas_primality 3463701263446490329787 (2 : ZMod 3463701263446490329787)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (89, 1), (467, 1), (621911721757133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463701263446490329787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_67
      · exact prime_twentyEightZ_89
      · exact prime_twentyEightZ_467
      · exact prime_twentyEightZ_621911721757133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3463701263446490329787) ^ 1731850631723245164893 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 51697033782783437758 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 38917991724117868874 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 7416919193675568158 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3463701263446490329787) ^ 5569442 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_4712696973609818164547 : Nat.Prime 4712696973609818164547 := by
  apply lucas_primality 4712696973609818164547 (2 : ZMod 4712696973609818164547)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) = 4712696973609818164547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_431
      · exact prime_twentyEightZ_3532679
      · exact prime_twentyEightZ_3139143389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4712696973609818164547) ^ 2356348486804909082273 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 277217469035871656738 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 162506792193442005674 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 10934331725312803166 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1334029209449774 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1501268463914 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_11380112522338097407091 : Nat.Prime 11380112522338097407091 := by
  apply lucas_primality 11380112522338097407091 (2 : ZMod 11380112522338097407091)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) = 11380112522338097407091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_67
      · exact prime_twentyEightZ_19379
      · exact prime_twentyEightZ_311677
      · exact prime_twentyEightZ_216317813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11380112522338097407091) ^ 5690056261169048703545 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 2276022504467619481418 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 875393270949084415930 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 169852425706538767270 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 587239409790912710 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 36512519442686170 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 52608300557930 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_12322133312567452318279 : Nat.Prime 12322133312567452318279 := by
  apply lucas_primality 12322133312567452318279 (3 : ZMod 12322133312567452318279)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (79, 1), (383, 1), (22624945031209403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (79, 1), (383, 1), (22624945031209403, 1)] : List FactorBlock).map factorBlockValue).prod) = 12322133312567452318279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_79
      · exact prime_twentyEightZ_383
      · exact prime_twentyEightZ_22624945031209403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12322133312567452318279) ^ 6161066656283726159139 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12322133312567452318279) ^ 4107377770855817439426 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12322133312567452318279) ^ 155976371045157624282 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12322133312567452318279) ^ 32172671834379771066 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12322133312567452318279) ^ 544626 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_14115836970606756764153 : Nat.Prime 14115836970606756764153 := by
  apply lucas_primality 14115836970606756764153 (3 : ZMod 14115836970606756764153)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1427, 1), (1236495880396527397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1427, 1), (1236495880396527397, 1)] : List FactorBlock).map factorBlockValue).prod) = 14115836970606756764153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_1427
      · exact prime_twentyEightZ_1236495880396527397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14115836970606756764153) ^ 7057918485303378382076 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14115836970606756764153) ^ 9891967043172219176 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14115836970606756764153) ^ 11416 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_26370944303301776617973 : Nat.Prime 26370944303301776617973 := by
  apply lucas_primality 26370944303301776617973 (3 : ZMod 26370944303301776617973)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1097, 1), (8861, 1), (5301631, 1), (9840643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1097, 1), (8861, 1), (5301631, 1), (9840643, 1)] : List FactorBlock).map factorBlockValue).prod) = 26370944303301776617973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_1097
      · exact prime_twentyEightZ_8861
      · exact prime_twentyEightZ_5301631
      · exact prime_twentyEightZ_9840643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26370944303301776617973) ^ 13185472151650888308986 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26370944303301776617973) ^ 2028534177177059739844 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26370944303301776617973) ^ 24039147040384481876 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26370944303301776617973) ^ 2976068649509285252 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26370944303301776617973) ^ 4974119153766412 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26370944303301776617973) ^ 2679798901687804 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_32457694465787711188511 : Nat.Prime 32457694465787711188511 := by
  apply lucas_primality 32457694465787711188511 (7 : ZMod 32457694465787711188511)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) = 32457694465787711188511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_6475879
      · exact prime_twentyEightZ_38554545693913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32457694465787711188511) ^ 16228847232893855594255 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 6491538893157542237702 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 2496745728137516245270 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 5012090940208690 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 841864270 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_50626684582777451757247 : Nat.Prime 50626684582777451757247 := by
  apply lucas_primality 50626684582777451757247 (6 : ZMod 50626684582777451757247)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (767070978526931087231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (767070978526931087231, 1)] : List FactorBlock).map factorBlockValue).prod) = 50626684582777451757247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_767070978526931087231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 50626684582777451757247) ^ 25313342291388725878623 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50626684582777451757247) ^ 16875561527592483919082 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50626684582777451757247) ^ 4602425871161586523386 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50626684582777451757247) ^ 66 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_64915388931575422377023 : Nat.Prime 64915388931575422377023 := by
  apply lucas_primality 64915388931575422377023 (5 : ZMod 64915388931575422377023)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) = 64915388931575422377023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_32457694465787711188511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64915388931575422377023) ^ 32457694465787711188511 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 64915388931575422377023) ^ 2 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_64924173686068701574919 : Nat.Prime 64924173686068701574919 := by
  apply lucas_primality 64924173686068701574919 (13 : ZMod 64924173686068701574919)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (59, 1), (67, 1), (118399, 1), (2391682846193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (59, 1), (67, 1), (118399, 1), (2391682846193, 1)] : List FactorBlock).map factorBlockValue).prod) = 64924173686068701574919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_67
      · exact prime_twentyEightZ_118399
      · exact prime_twentyEightZ_2391682846193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 64924173686068701574919) ^ 32462086843034350787459 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 64924173686068701574919) ^ 2238764609864437985342 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 64924173686068701574919) ^ 1100409723492689857202 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 64924173686068701574919) ^ 969017517702517933954 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 64924173686068701574919) ^ 548350692878053882 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 64924173686068701574919) ^ 27145812326 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_118277801317280051344753 : Nat.Prime 118277801317280051344753 := by
  apply lucas_primality 118277801317280051344753 (5 : ZMod 118277801317280051344753)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (71, 1), (4451, 1), (7797332648072969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (71, 1), (4451, 1), (7797332648072969, 1)] : List FactorBlock).map factorBlockValue).prod) = 118277801317280051344753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_71
      · exact prime_twentyEightZ_4451
      · exact prime_twentyEightZ_7797332648072969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 118277801317280051344753) ^ 59138900658640025672376 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 118277801317280051344753) ^ 39425933772426683781584 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 118277801317280051344753) ^ 1665884525595493680912 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 118277801317280051344753) ^ 26573309664632678352 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 118277801317280051344753) ^ 15169008 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_291830251554904380435479 : Nat.Prime 291830251554904380435479 := by
  apply lucas_primality 291830251554904380435479 (13 : ZMod 291830251554904380435479)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17290739, 1), (8438917837893001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17290739, 1), (8438917837893001, 1)] : List FactorBlock).map factorBlockValue).prod) = 291830251554904380435479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_17290739
      · exact prime_twentyEightZ_8438917837893001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 291830251554904380435479) ^ 145915125777452190217739 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 291830251554904380435479) ^ 16877835675786002 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (13 : ZMod 291830251554904380435479) ^ 34581478 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod) = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_3061
      · exact prime_twentyEightZ_61379
      · exact prime_twentyEightZ_382747
      · exact prime_twentyEightZ_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 621509730110564998034623) ^ 310754865055282499017311 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 207169910036854999344874 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 203041401538897418502 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 10125771519747226218 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 1623813459310105626 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 621509730110564998034623) ^ 431465607923358 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1294064843238302782937263 : Nat.Prime 1294064843238302782937263 := by
  apply lucas_primality 1294064843238302782937263 (3 : ZMod 1294064843238302782937263)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (29, 1), (151778658601724464337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (29, 1), (151778658601724464337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1294064843238302782937263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_151778658601724464337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1294064843238302782937263) ^ 647032421619151391468631 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1294064843238302782937263) ^ 431354947746100927645754 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1294064843238302782937263) ^ 184866406176900397562466 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1294064843238302782937263) ^ 44622925628906992515078 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1294064843238302782937263) ^ 8526 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1449300501505145286560051 : Nat.Prime 1449300501505145286560051 := by
  apply lucas_primality 1449300501505145286560051 (6 : ZMod 1449300501505145286560051)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1449300501505145286560051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_1321
      · exact prime_twentyEightZ_1255074433
      · exact prime_twentyEightZ_17483007257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1449300501505145286560051) ^ 724650250752572643280025 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 289860100301029057312010 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1097123771010708014050 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 1154752629324850 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1449300501505145286560051) ^ 82897666299650 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_5252018523699670552168511 : Nat.Prime 5252018523699670552168511 := by
  apply lucas_primality 5252018523699670552168511 (7 : ZMod 5252018523699670552168511)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (7823, 1), (1612937, 1), (2190694981879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (7823, 1), (1612937, 1), (2190694981879, 1)] : List FactorBlock).map factorBlockValue).prod) = 5252018523699670552168511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_7823
      · exact prime_twentyEightZ_1612937
      · exact prime_twentyEightZ_2190694981879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5252018523699670552168511) ^ 2626009261849835276084255 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5252018523699670552168511) ^ 1050403704739934110433702 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5252018523699670552168511) ^ 276422027563140555377290 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5252018523699670552168511) ^ 671356068477524038370 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5252018523699670552168511) ^ 3256183300215489230 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5252018523699670552168511) ^ 2397421168690 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_5360018256942847067732857 : Nat.Prime 5360018256942847067732857 := by
  apply lucas_primality 5360018256942847067732857 (5 : ZMod 5360018256942847067732857)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) = 5360018256942847067732857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_239
      · exact prime_twentyEightZ_4519
      · exact prime_twentyEightZ_15661
      · exact prime_twentyEightZ_13203689273969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5360018256942847067732857) ^ 2680009128471423533866428 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1786672752314282355910952 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 22426854631560029572104 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1186107160199789127624 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 342252618411522065496 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 405948530424 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_9858091946062842016175737 : Nat.Prime 9858091946062842016175737 := by
  apply lucas_primality 9858091946062842016175737 (10 : ZMod 9858091946062842016175737)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4703, 1), (215497, 1), (135096519595393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4703, 1), (215497, 1), (135096519595393, 1)] : List FactorBlock).map factorBlockValue).prod) = 9858091946062842016175737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_4703
      · exact prime_twentyEightZ_215497
      · exact prime_twentyEightZ_135096519595393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 9858091946062842016175737) ^ 4929045973031421008087868 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 3286030648687614005391912 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 2096128417193885183112 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 45745843079313596088 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 72970732152 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_16061849953847172969586669 : Nat.Prime 16061849953847172969586669 := by
  apply lucas_primality 16061849953847172969586669 (2 : ZMod 16061849953847172969586669)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (1229, 1), (19106783380496639413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (1229, 1), (19106783380496639413, 1)] : List FactorBlock).map factorBlockValue).prod) = 16061849953847172969586669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_1229
      · exact prime_twentyEightZ_19106783380496639413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16061849953847172969586669) ^ 8030924976923586484793334 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 16061849953847172969586669) ^ 5353949984615724323195556 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 16061849953847172969586669) ^ 845360523886693314188772 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 16061849953847172969586669) ^ 13069039832259701358492 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 16061849953847172969586669) ^ 840636 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_18597456603864619938380969 : Nat.Prime 18597456603864619938380969 := by
  apply lucas_primality 18597456603864619938380969 (3 : ZMod 18597456603864619938380969)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) = 18597456603864619938380969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_1173959
      · exact prime_twentyEightZ_180018837229260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18597456603864619938380969) ^ 9298728301932309969190484 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 1690677873078601812580088 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 15841657676174908952 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 103308392 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_20135932332651474142529273 : Nat.Prime 20135932332651474142529273 := by
  apply lucas_primality 20135932332651474142529273 (3 : ZMod 20135932332651474142529273)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) = 20135932332651474142529273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_991
      · exact prime_twentyEightZ_3779417
      · exact prime_twentyEightZ_39530687550041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20135932332651474142529273) ^ 10067966166325737071264636 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 1184466607803027890737016 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 20318801546570609629192 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 5327787945244325816 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 509374705592 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_303701584907147004498331421 : Nat.Prime 303701584907147004498331421 := by
  apply lucas_primality 303701584907147004498331421 (2 : ZMod 303701584907147004498331421)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1217, 1), (2861, 1), (3581, 1), (1217879459003443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1217, 1), (2861, 1), (3581, 1), (1217879459003443, 1)] : List FactorBlock).map factorBlockValue).prod) = 303701584907147004498331421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_1217
      · exact prime_twentyEightZ_2861
      · exact prime_twentyEightZ_3581
      · exact prime_twentyEightZ_1217879459003443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 303701584907147004498331421) ^ 151850792453573502249165710 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 303701584907147004498331421) ^ 60740316981429400899666284 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 303701584907147004498331421) ^ 249549371328797867295260 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 303701584907147004498331421) ^ 106152249181106957182220 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 303701584907147004498331421) ^ 84809155237963419295820 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (2 : ZMod 303701584907147004498331421) ^ 249369165940 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_344827841196656494690813801 : Nat.Prime 344827841196656494690813801 := by
  apply lucas_primality 344827841196656494690813801 (97 : ZMod 344827841196656494690813801)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 344827841196656494690813801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 344827841196656494690813801) ^ 172413920598328247345406900 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 114942613732218831563604600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 68965568239331298938162760 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 49261120170950927812973400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 31347985563332408608255800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 26525218553588961130062600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 20283990658626852628871400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 18148833747192447088990200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 14992514834637238899600600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 11890615213677810161752200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 11123478748279241764219800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 9319671383693418775427400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 8410435151137963285141800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 8019252120852476620716600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 7336762578652265844485400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 6506185682955782918694600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 5844539681299262621878200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 344827841196656494690813801) ^ 5652915429453385158865800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_376175826759988903299069601 : Nat.Prime 376175826759988903299069601 := by
  apply lucas_primality 376175826759988903299069601 (33 : ZMod 376175826759988903299069601)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 376175826759988903299069601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 376175826759988903299069601) ^ 188087913379994451649534800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 125391942253329634433023200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 75235165351997780659813920 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 53739403822855557614152800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 28936602058460684869159200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 22127989809411111958768800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 19798727724209942278898400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 16355470728695169708655200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 12971580233103065631002400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 12134704089031900106421600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 10166914236756456845920800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 9175020164877778129245600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 8748275040929974495327200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 8003740994893380921256800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 7097657108679035911303200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 6375861470508286496594400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (33 : ZMod 376175826759988903299069601) ^ 6166816832130965627853600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_389452620645635570474330881 : Nat.Prime 389452620645635570474330881 := by
  apply lucas_primality 389452620645635570474330881 (67 : ZMod 389452620645635570474330881)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 1), (7, 3), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 1), (7, 3), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 389452620645635570474330881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 389452620645635570474330881) ^ 194726310322817785237165440 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 129817540215211856824776960 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 77890524129127114094866176 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 55636088663662224353475840 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 35404783695057779134030080 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 29957893895818120805717760 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 20497506349770293182859520 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 16932722636766763933666560 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 13429400711918467947390720 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 12562987762762437757236480 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 10525746503936096499306240 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 9498844405991111474983680 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 9057037689433385359868160 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 8286225971183735542007040 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 7348162653691237178760960 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 6600891875349755431768320 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (67 : ZMod 389452620645635570474330881) ^ 6384469190912058532366080 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 525451948490143230005049601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (179 : ZMod 525451948490143230005049601) ^ 262725974245071615002524800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 175150649496714410001683200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 105090389698028646001009920 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 75064564070020461429292800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 47768358953649384545913600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 40419380653087940769619200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 30908938146479013529708800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 27655365710007538421318400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 22845736890875792608915200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 18119032706556663103622400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 16950062854520749355001600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 14201404013247114324460800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12815901182686420244025600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 12219812755584726279187200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 11179828691279643191596800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 9914187707361193018963200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8905965228646495423814400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (179 : ZMod 525451948490143230005049601) ^ 8613966368690872623033600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_580762679910158306847686401 : Nat.Prime 580762679910158306847686401 := by
  apply lucas_primality 580762679910158306847686401 (19 : ZMod 580762679910158306847686401)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 580762679910158306847686401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 580762679910158306847686401) ^ 290381339955079153423843200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 193587559970052768949228800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 116152535982031661369537280 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 82966097130022615263955200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 52796607264559846077062400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 44674052300781408219052800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 34162510582950488638099200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 25250551300441665515116800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 20026299307246838167161600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 18734279997101880866054400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 15696288646220494779667200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 14164943412442885532870400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 13506108835119960624364800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 12356652764045921422291200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 10957786413399213336748800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 9843435252714547573689600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (19 : ZMod 580762679910158306847686401) ^ 9520699670658332899142400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_704329207550617521070598401 : Nat.Prime 704329207550617521070598401 := by
  apply lucas_primality 704329207550617521070598401 (79 : ZMod 704329207550617521070598401)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 704329207550617521070598401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 704329207550617521070598401) ^ 352164603775308760535299200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 234776402516872507023532800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 140865841510123504214119680 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 100618458221516788724371200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 64029927959147047370054400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 54179169811585963159276800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 41431129855918677710035200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 37069958292137764266873600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 30623009023939892220460800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 24287214053469569692089600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 22720297017761855518406400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 19035924528395068137043200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 17178761159771159050502400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 16379749012805058629548800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 13289230331143726812652800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 11937783178824025780857600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (79 : ZMod 704329207550617521070598401) ^ 11546380451649467558534400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_752351653519977806598139201 : Nat.Prime 752351653519977806598139201 := by
  apply lucas_primality 752351653519977806598139201 (22 : ZMod 752351653519977806598139201)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 752351653519977806598139201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 752351653519977806598139201) ^ 376175826759988903299069600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 250783884506659268866046400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 150470330703995561319627840 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 107478807645711115228305600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 57873204116921369738318400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 44255979618822223917537600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 39597455448419884557796800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 32710941457390339417310400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 25943160466206131262004800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 24269408178063800212843200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 20333828473512913691841600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 18350040329755556258491200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 17496550081859948990654400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 16007481989786761842513600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 14195314217358071822606400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12751722941016572993188800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12333633664261931255707200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_919540909857750652508836801 : Nat.Prime 919540909857750652508836801 := by
  apply lucas_primality 919540909857750652508836801 (113 : ZMod 919540909857750652508836801)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 919540909857750652508836801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 919540909857750652508836801) ^ 459770454928875326254418400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 306513636619250217502945600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 183908181971550130501767360 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 83594628168886422955348800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 70733916142903896346833600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 54090641756338273676990400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 48396889992513192237307200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 39980039559032637065601600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 31708307236474160431339200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 29662609995411311371252800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 24852457023182450067806400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 22427827069701235427044800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 21384672322273270988577600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 19564700209739375585294400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 17349828487882087783185600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15585439150131366991675200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15074441145209027090308800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1226054546477000870011782401 : Nat.Prime 1226054546477000870011782401 := by
  apply lucas_primality 1226054546477000870011782401 (3 : ZMod 1226054546477000870011782401)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226054546477000870011782401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1226054546477000870011782401) ^ 613027273238500435005891200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 245210909295400174002356480 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 175150649496714410001683200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 111459504225181897273798400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 94311888190538528462444800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 72120855675117698235987200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 64529186656684256316409600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 53306719412043516087468800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 42277742981965547241785600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 39550146660548415161670400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 33136609364243266757075200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 29903769426268313902726400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 28512896429697694651436800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 26086266946319167447059200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 23133104650509450377580800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 20780585533508489322233600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1226054546477000870011782401) ^ 20099254860278702787078400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429690015148801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_11
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 1576355845470429690015148801) ^ 788177922735214845007574400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 525451948490143230005049600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 315271169094085938003029760 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 225193692210061384287878400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 143305076860948153637740800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 121258141959263822308857600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 92726814439437040589126400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 82966097130022615263955200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 68537210672627377826745600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 54357098119669989310867200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 50850188563562248065004800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 42604212039741342973382400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 38447703548059260732076800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 36659438266754178837561600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 33539486073838929574790400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 29742563122083579056889600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 26717895685939486271443200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (101 : ZMod 1576355845470429690015148801) ^ 25841899106072617869100800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem prime_twentyEightZ_3009406614079911226392556801 : Nat.Prime 3009406614079911226392556801 := by
  apply lucas_primality 3009406614079911226392556801 (97 : ZMod 3009406614079911226392556801)
  · rw [← twentyEightZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3009406614079911226392556801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_twentyEightZ_2
      · exact prime_twentyEightZ_3
      · exact prime_twentyEightZ_5
      · exact prime_twentyEightZ_7
      · exact prime_twentyEightZ_13
      · exact prime_twentyEightZ_17
      · exact prime_twentyEightZ_19
      · exact prime_twentyEightZ_23
      · exact prime_twentyEightZ_29
      · exact prime_twentyEightZ_31
      · exact prime_twentyEightZ_37
      · exact prime_twentyEightZ_41
      · exact prime_twentyEightZ_43
      · exact prime_twentyEightZ_47
      · exact prime_twentyEightZ_53
      · exact prime_twentyEightZ_59
      · exact prime_twentyEightZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 3009406614079911226392556801) ^ 1504703307039955613196278400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 1003135538026637075464185600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 601881322815982245278511360 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 429915230582844460913222400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 231492816467685478953273600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 177023918475288895670150400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 158389821793679538231187200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 130843765829561357669241600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 103772641864824525048019200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 97077632712255200851372800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 81335313894051654767366400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 73400161319022225033964800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 69986200327439795962617600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 64029927959147047370054400 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 56781256869432287290425600 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 51006891764066291972755200 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide
    · change (97 : ZMod 3009406614079911226392556801) ^ 49334534657047725022828800 ≠ 1
      rw [← twentyEightZFastPow_eq_pow]
      decide

private theorem phi_twentyEightZ_33103472754879023490318124800 : Nat.totient 33103472754879023490318124800 = 4355998316862097902796800000 := by
  rw [← show ((([(2, 8), (3, 3), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_5, prime_twentyEightZ_7, prime_twentyEightZ_11, prime_twentyEightZ_13, prime_twentyEightZ_17, prime_twentyEightZ_19, prime_twentyEightZ_23, prime_twentyEightZ_29, prime_twentyEightZ_31, prime_twentyEightZ_37, prime_twentyEightZ_41, prime_twentyEightZ_43, prime_twentyEightZ_47, prime_twentyEightZ_53, prime_twentyEightZ_59, prime_twentyEightZ_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124801 : Nat.totient 33103472754879023490318124801 = 33103407830705337421616040004 := by
  rw [← show ((([(509879, 1), (64924173686068701574919, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_509879, prime_twentyEightZ_64924173686068701574919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124802 : Nat.totient 33103472754879023490318124802 = 16487838943942525052785605120 := by
  rw [← show ((([(2, 1), (269, 1), (7691, 1), (111869, 1), (218857, 1), (326767060643, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_269, prime_twentyEightZ_7691, prime_twentyEightZ_111869, prime_twentyEightZ_218857, prime_twentyEightZ_326767060643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124803 : Nat.totient 33103472754879023490318124803 = 22066393706899539054646191624 := by
  rw [← show ((([(3, 1), (8527, 1), (1294064843238302782937263, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_8527, prime_twentyEightZ_1294064843238302782937263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124804 : Nat.totient 33103472754879023490318124804 = 16551606546661648594314053384 := by
  rw [← show ((([(2, 2), (127487, 1), (64915388931575422377023, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_127487, prime_twentyEightZ_64915388931575422377023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124805 : Nat.totient 33103472754879023490318124805 = 26482495659514424750867391360 := by
  rw [← show ((([(5, 1), (93787, 1), (153198571, 1), (460793340036793, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_5, prime_twentyEightZ_93787, prime_twentyEightZ_153198571, prime_twentyEightZ_460793340036793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124806 : Nat.totient 33103472754879023490318124806 = 10966794654856099114012645440 := by
  rw [← show ((([(2, 1), (3, 1), (163, 1), (81554969011, 1), (415034571917257, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_163, prime_twentyEightZ_81554969011, prime_twentyEightZ_415034571917257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124807 : Nat.totient 33103472754879023490318124807 = 28300557797673049044347904000 := by
  rw [← show ((([(7, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_7, prime_twentyEightZ_401, prime_twentyEightZ_11069, prime_twentyEightZ_53269, prime_twentyEightZ_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124808 : Nat.totient 33103472754879023490318124808 = 16551690856989422392767979600 := by
  rw [← show ((([(2, 3), (363611, 1), (11380112522338097407091, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_363611, prime_twentyEightZ_11380112522338097407091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124809 : Nat.totient 33103472754879023490318124809 = 21972610736862932622394561824 := by
  rw [← show ((([(3, 2), (229, 1), (16061849953847172969586669, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_229, prime_twentyEightZ_16061849953847172969586669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124810 : Nat.totient 33103472754879023490318124810 = 13227264892236486626093133120 := by
  rw [← show ((([(2, 1), (5, 1), (1667, 1), (2141, 1), (927515741733830445223, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_5, prime_twentyEightZ_1667, prime_twentyEightZ_2141, prime_twentyEightZ_927515741733830445223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124811 : Nat.totient 33103472754879023490318124811 = 30094066140799112263925568000 := by
  rw [← show ((([(11, 1), (3009406614079911226392556801, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_11, prime_twentyEightZ_3009406614079911226392556801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124812 : Nat.totient 33103472754879023490318124812 = 10953947188962401933535923968 := by
  rw [← show ((([(2, 2), (3, 1), (137, 1), (20135932332651474142529273, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_137, prime_twentyEightZ_20135932332651474142529273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124813 : Nat.totient 33103472754879023490318124813 = 30557051773733205476848350000 := by
  rw [← show ((([(13, 1), (36268517031751, 1), (70210231615351, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_13, prime_twentyEightZ_36268517031751, prime_twentyEightZ_70210231615351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124814 : Nat.totient 33103472754879023490318124814 = 14187135113158311726045645312 := by
  rw [← show ((([(2, 1), (7, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_7, prime_twentyEightZ_210193, prime_twentyEightZ_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124815 : Nat.totient 33103472754879023490318124815 = 17655182008742706505462981152 := by
  rw [← show ((([(3, 1), (5, 1), (5101879, 1), (432565763252833233799, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_5, prime_twentyEightZ_5101879, prime_twentyEightZ_432565763252833233799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124816 : Nat.totient 33103472754879023490318124816 = 16543997288938364065731985536 := by
  rw [← show ((([(2, 4), (3023, 1), (7309, 1), (93639150386551147643, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3023, prime_twentyEightZ_7309, prime_twentyEightZ_93639150386551147643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124817 : Nat.totient 33103472754879023490318124817 = 31156205889198669547486775040 := by
  rw [← show ((([(17, 1), (8522119, 1), (292575589, 1), (780978274411, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_17, prime_twentyEightZ_8522119, prime_twentyEightZ_292575589, prime_twentyEightZ_780978274411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124818 : Nat.totient 33103472754879023490318124818 = 10978476427164975651883134720 := by
  rw [← show ((([(2, 1), (3, 2), (197, 1), (5944361, 1), (1570470015063981253, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_197, prime_twentyEightZ_5944361, prime_twentyEightZ_1570470015063981253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124819 : Nat.totient 33103472754879023490318124819 = 30881145524579043607904256000 := by
  rw [← show ((([(19, 1), (71, 1), (811, 1), (149153, 1), (189324997, 1), (1071521281, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_19, prime_twentyEightZ_71, prime_twentyEightZ_811, prime_twentyEightZ_149153, prime_twentyEightZ_189324997, prime_twentyEightZ_1071521281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124820 : Nat.totient 33103472754879023490318124820 = 13092609449120692436620201472 := by
  rw [← show ((([(2, 2), (5, 1), (89, 1), (18597456603864619938380969, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_5, prime_twentyEightZ_89, prime_twentyEightZ_18597456603864619938380969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124821 : Nat.totient 33103472754879023490318124821 = 18916270145645156280181785600 := by
  rw [← show ((([(3, 1), (7, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_7, prime_twentyEightZ_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124822 : Nat.totient 33103472754879023490318124822 = 15020085351868930137738700800 := by
  rw [← show ((([(2, 1), (11, 1), (643, 1), (4289, 1), (344543, 1), (1583581521533941, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_11, prime_twentyEightZ_643, prime_twentyEightZ_4289, prime_twentyEightZ_344543, prime_twentyEightZ_1583581521533941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124823 : Nat.totient 33103472754879023490318124823 = 31664139326162857078494481024 := by
  rw [← show ((([(23, 1), (608873, 1), (2363845045067156754137, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_23, prime_twentyEightZ_608873, prime_twentyEightZ_2363845045067156754137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124824 : Nat.totient 33103472754879023490318124824 = 10992151663418071671083919360 := by
  rw [← show ((([(2, 3), (3, 1), (263, 1), (33811, 1), (189853, 1), (817016986973969, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_263, prime_twentyEightZ_33811, prime_twentyEightZ_189853, prime_twentyEightZ_817016986973969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124825 : Nat.totient 33103472754879023490318124825 = 26397622209247247565556713600 := by
  rw [← show ((([(5, 2), (311, 1), (11152399, 1), (381772691531587337, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_5, prime_twentyEightZ_311, prime_twentyEightZ_11152399, prime_twentyEightZ_381772691531587337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124826 : Nat.totient 33103472754879023490318124826 = 15278525886866354752650863664 := by
  rw [← show ((([(2, 1), (13, 1), (27346626158783, 1), (46558229274047, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_13, prime_twentyEightZ_27346626158783, prime_twentyEightZ_46558229274047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124827 : Nat.totient 33103472754879023490318124827 = 22068981836586015660212083200 := by
  rw [← show ((([(3, 3), (1226054546477000870011782401, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_1226054546477000870011782401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124828 : Nat.totient 33103472754879023490318124828 = 14046657934239547674011714304 := by
  rw [← show ((([(2, 2), (7, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_7, prime_twentyEightZ_103, prime_twentyEightZ_5009, prime_twentyEightZ_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124829 : Nat.totient 33103472754879023490318124829 = 31810146368860280384887472640 := by
  rw [← show ((([(29, 1), (211, 1), (91229, 1), (359085967, 1), (165143602937, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_29, prime_twentyEightZ_211, prime_twentyEightZ_91229, prime_twentyEightZ_359085967, prime_twentyEightZ_165143602937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124830 : Nat.totient 33103472754879023490318124830 = 8827591150608196735793153696 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (5572883, 1), (198003276191030887067, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_5, prime_twentyEightZ_5572883, prime_twentyEightZ_198003276191030887067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124831 : Nat.totient 33103472754879023490318124831 = 32015610515930763018615552000 := by
  rw [← show ((([(31, 1), (1789, 1), (15241, 1), (61623641, 1), (635536801589, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_31, prime_twentyEightZ_1789, prime_twentyEightZ_15241, prime_twentyEightZ_61623641, prime_twentyEightZ_635536801589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124832 : Nat.totient 33103472754879023490318124832 = 16465976085328426192075333632 := by
  rw [← show ((([(2, 5), (193, 1), (5360018256942847067732857, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_193, prime_twentyEightZ_5360018256942847067732857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124833 : Nat.totient 33103472754879023490318124833 = 19957670390058748098240338000 := by
  rw [← show ((([(3, 1), (11, 1), (191, 1), (5252018523699670552168511, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_11, prime_twentyEightZ_191, prime_twentyEightZ_5252018523699670552168511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124834 : Nat.totient 33103472754879023490318124834 = 15576074152088802025107456000 := by
  rw [← show ((([(2, 1), (17, 1), (7681, 1), (6135331, 1), (20660407174714891, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_17, prime_twentyEightZ_7681, prime_twentyEightZ_6135331, prime_twentyEightZ_20660407174714891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124835 : Nat.totient 33103472754879023490318124835 = 22465180138713717417359424000 := by
  rw [← show ((([(5, 1), (7, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_5, prime_twentyEightZ_7, prime_twentyEightZ_107, prime_twentyEightZ_1013, prime_twentyEightZ_144417341, prime_twentyEightZ_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124836 : Nat.totient 33103472754879023490318124836 = 11034490918293007830106041600 := by
  rw [← show ((([(2, 2), (3, 2), (919540909857750652508836801, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_919540909857750652508836801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124837 : Nat.totient 33103472754879023490318124837 = 32201626705360065713208375360 := by
  rw [← show ((([(37, 1), (5581, 1), (23227, 1), (6901868647270889023, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_37, prime_twentyEightZ_5581, prime_twentyEightZ_23227, prime_twentyEightZ_6901868647270889023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124838 : Nat.totient 33103472754879023490318124838 = 15667427900794711599210931200 := by
  rw [← show ((([(2, 1), (19, 1), (1201, 1), (201823, 1), (512903, 1), (7007144209529, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_19, prime_twentyEightZ_1201, prime_twentyEightZ_201823, prime_twentyEightZ_512903, prime_twentyEightZ_7007144209529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124839 : Nat.totient 33103472754879023490318124839 = 20230822510648240089714048000 := by
  rw [← show ((([(3, 1), (13, 1), (151, 1), (3779, 1), (72089, 1), (20634127459681621, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_13, prime_twentyEightZ_151, prime_twentyEightZ_3779, prime_twentyEightZ_72089, prime_twentyEightZ_20634127459681621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124840 : Nat.totient 33103472754879023490318124840 = 13104633240301487415494860800 := by
  rw [← show ((([(2, 3), (5, 1), (97, 1), (72973, 1), (195271, 1), (598744972004371, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_5, prime_twentyEightZ_97, prime_twentyEightZ_72973, prime_twentyEightZ_195271, prime_twentyEightZ_598744972004371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124841 : Nat.totient 33103472754879023490318124841 = 32115433379431565307088926720 := by
  rw [← show ((([(41, 1), (179, 1), (157177, 1), (3871433, 1), (7412691492859, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_41, prime_twentyEightZ_179, prime_twentyEightZ_157177, prime_twentyEightZ_3871433, prime_twentyEightZ_7412691492859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124842 : Nat.totient 33103472754879023490318124842 = 9429298375565393472865536000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_7, prime_twentyEightZ_421, prime_twentyEightZ_1483, prime_twentyEightZ_2072201, prime_twentyEightZ_2567179, prime_twentyEightZ_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124843 : Nat.totient 33103472754879023490318124843 = 32333624403277436947781222184 := by
  rw [← show ((([(43, 1), (218470807, 1), (3523803542327912743, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_43, prime_twentyEightZ_218470807, prime_twentyEightZ_3523803542327912743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124844 : Nat.totient 33103472754879023490318124844 = 15047033070399556131962784000 := by
  rw [← show ((([(2, 2), (11, 1), (752351653519977806598139201, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_11, prime_twentyEightZ_752351653519977806598139201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124845 : Nat.totient 33103472754879023490318124845 = 17655184408872920582098741248 := by
  rw [← show ((([(3, 2), (5, 1), (16649617, 1), (44183162164402972273, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_5, prime_twentyEightZ_16649617, prime_twentyEightZ_44183162164402972273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124846 : Nat.totient 33103472754879023490318124846 = 15615217642563541753622365824 := by
  rw [← show ((([(2, 1), (23, 1), (73, 1), (9858091946062842016175737, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_23, prime_twentyEightZ_73, prime_twentyEightZ_9858091946062842016175737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124847 : Nat.totient 33103472754879023490318124847 = 32399143547328405969247526400 := by
  rw [← show ((([(47, 1), (704329207550617521070598401, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_47, prime_twentyEightZ_704329207550617521070598401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124848 : Nat.totient 33103472754879023490318124848 = 10903261327251748374695526400 := by
  rw [← show ((([(2, 4), (3, 1), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_131, prime_twentyEightZ_233, prime_twentyEightZ_550990241, prime_twentyEightZ_41007301887107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124849 : Nat.totient 33103472754879023490318124849 = 28348301809803090690355178664 := by
  rw [← show ((([(7, 2), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_7, prime_twentyEightZ_1087, prime_twentyEightZ_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124850 : Nat.totient 33103472754879023490318124850 = 13241077268160144507113903040 := by
  rw [← show ((([(2, 1), (5, 2), (42463, 1), (102310987907, 1), (152394958517, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_5, prime_twentyEightZ_42463, prime_twentyEightZ_102310987907, prime_twentyEightZ_152394958517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124851 : Nat.totient 33103472754879023490318124851 = 20770806299375789037848366592 := by
  rw [← show ((([(3, 1), (17, 2), (153791629, 1), (248268580828039157, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_17, prime_twentyEightZ_153791629, prime_twentyEightZ_248268580828039157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124852 : Nat.totient 33103472754879023490318124852 = 15277055525411475347645477280 := by
  rw [← show ((([(2, 2), (13, 2), (10391, 1), (4712696973609818164547, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_13, prime_twentyEightZ_10391, prime_twentyEightZ_4712696973609818164547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124853 : Nat.totient 33103472754879023490318124853 = 32344560747345158769269869056 := by
  rw [← show ((([(53, 1), (397, 1), (617, 1), (2549893347446836525949, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_53, prime_twentyEightZ_397, prime_twentyEightZ_617, prime_twentyEightZ_2549893347446836525949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124854 : Nat.totient 33103472754879023490318124854 = 11033316098868550709001686400 := by
  rw [← show ((([(2, 1), (3, 4), (10141, 1), (127241, 1), (158361893331124207, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_10141, prime_twentyEightZ_127241, prime_twentyEightZ_158361893331124207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124855 : Nat.totient 33103472754879023490318124855 = 24067153592620773579820800000 := by
  rw [← show ((([(5, 1), (11, 1), (3001, 1), (317971, 1), (19742057, 1), (31949565563, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_5, prime_twentyEightZ_11, prime_twentyEightZ_3001, prime_twentyEightZ_317971, prime_twentyEightZ_19742057, prime_twentyEightZ_31949565563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124856 : Nat.totient 33103472754879023490318124856 = 14187202597629893889172946400 := by
  rw [← show ((([(2, 3), (7, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_7, prime_twentyEightZ_1222615931, prime_twentyEightZ_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124857 : Nat.totient 33103472754879023490318124857 = 20907456476765699046516710400 := by
  rw [← show ((([(3, 1), (19, 1), (580762679910158306847686401, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_19, prime_twentyEightZ_580762679910158306847686401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124858 : Nat.totient 33103472754879023490318124858 = 15980986753169035239071032176 := by
  rw [← show ((([(2, 1), (29, 1), (169985287, 1), (3357640771913012023, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_29, prime_twentyEightZ_169985287, prime_twentyEightZ_3357640771913012023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124859 : Nat.totient 33103472754879023490318124859 = 31938399143337214084435195680 := by
  rw [← show ((([(59, 1), (67, 1), (271, 1), (1796794919, 1), (17198039427347, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_59, prime_twentyEightZ_67, prime_twentyEightZ_271, prime_twentyEightZ_1796794919, prime_twentyEightZ_17198039427347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124860 : Nat.totient 33103472754879023490318124860 = 8827592734280073361961454912 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (24913302187, 1), (22145781469408963, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_5, prime_twentyEightZ_24913302187, prime_twentyEightZ_22145781469408963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124861 : Nat.totient 33103472754879023490318124861 = 32463031891406425161863270400 := by
  rw [← show ((([(61, 1), (337, 1), (29867, 1), (596081, 1), (90451742869699, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_61, prime_twentyEightZ_337, prime_twentyEightZ_29867, prime_twentyEightZ_596081, prime_twentyEightZ_90451742869699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124862 : Nat.totient 33103472754879023490318124862 = 15890611991860846144983859200 := by
  rw [← show ((([(2, 1), (31, 1), (139, 1), (1381, 1), (35747, 1), (10167809, 1), (7652554093, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_31, prime_twentyEightZ_139, prime_twentyEightZ_1381, prime_twentyEightZ_35747, prime_twentyEightZ_10167809, prime_twentyEightZ_7652554093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124863 : Nat.totient 33103472754879023490318124863 = 18916270145645156280181785600 := by
  rw [← show ((([(3, 2), (7, 1), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_7, prime_twentyEightZ_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124864 : Nat.totient 33103472754879023490318124864 = 16339597154564897015566073856 := by
  rw [← show ((([(2, 6), (79, 1), (6229, 1), (8696692033, 1), (120863194567, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_79, prime_twentyEightZ_6229, prime_twentyEightZ_8696692033, prime_twentyEightZ_120863194567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124865 : Nat.totient 33103472754879023490318124865 = 24438951387859104335928775680 := by
  rw [← show ((([(5, 1), (13, 1), (4657, 1), (16963, 1), (6446905430873149531, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_5, prime_twentyEightZ_13, prime_twentyEightZ_4657, prime_twentyEightZ_16963, prime_twentyEightZ_6446905430873149531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124866 : Nat.totient 33103472754879023490318124866 = 10031287845878438681345667840 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (148537, 1), (3376719396603664660873, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_11, prime_twentyEightZ_148537, prime_twentyEightZ_3376719396603664660873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124867 : Nat.totient 33103472754879023490318124867 = 33103472754878630346814415200 := by
  rw [← show ((([(122160859692467, 1), (270982644017201, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_122160859692467, prime_twentyEightZ_270982644017201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124868 : Nat.totient 33103472754879023490318124868 = 15578093255058884506772002304 := by
  rw [← show ((([(2, 2), (17, 1), (1346333, 1), (361586454322254942197, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_17, prime_twentyEightZ_1346333, prime_twentyEightZ_361586454322254942197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124869 : Nat.totient 33103472754879023490318124869 = 21109332179577136906104447600 := by
  rw [← show ((([(3, 1), (23, 1), (164011, 1), (2925172547624193772291, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_23, prime_twentyEightZ_164011, prime_twentyEightZ_2925172547624193772291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124870 : Nat.totient 33103472754879023490318124870 = 11299652204252097710385228672 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_5, prime_twentyEightZ_7, prime_twentyEightZ_239, prime_twentyEightZ_4327, prime_twentyEightZ_1214459, prime_twentyEightZ_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124871 : Nat.totient 33103472754879023490318124871 = 33072862496814386769760204800 := by
  rw [← show ((([(1091, 1), (221657, 1), (278561, 1), (491413453268053, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_1091, prime_twentyEightZ_221657, prime_twentyEightZ_278561, prime_twentyEightZ_491413453268053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124872 : Nat.totient 33103472754879023490318124872 = 11005731768077896458884520960 := by
  rw [← show ((([(2, 3), (3, 2), (521, 1), (1453, 1), (607348163015529886877, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_521, prime_twentyEightZ_1453, prime_twentyEightZ_607348163015529886877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124873 : Nat.totient 33103472754879023490318124873 = 33103446383934720188540251600 := by
  rw [← show ((([(1255301, 1), (26370944303301776617973, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_1255301, prime_twentyEightZ_26370944303301776617973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124874 : Nat.totient 33103472754879023490318124874 = 16091987193044236941433242624 := by
  rw [← show ((([(2, 1), (37, 1), (2063, 1), (3539, 1), (360037, 1), (3015373, 1), (56438293, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_37, prime_twentyEightZ_2063, prime_twentyEightZ_3539, prime_twentyEightZ_360037, prime_twentyEightZ_3015373, prime_twentyEightZ_56438293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124875 : Nat.totient 33103472754879023490318124875 = 17649282789305696858855465600 := by
  rw [← show ((([(3, 1), (5, 3), (2999, 1), (1127333, 1), (26110404665159999, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_5, prime_twentyEightZ_2999, prime_twentyEightZ_1127333, prime_twentyEightZ_26110404665159999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124876 : Nat.totient 33103472754879023490318124876 = 15680592353462415706736672400 := by
  rw [← show ((([(2, 2), (19, 1), (3813504911, 1), (114218290024018991, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_19, prime_twentyEightZ_3813504911, prime_twentyEightZ_114218290024018991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124877 : Nat.totient 33103472754879023490318124877 = 25790285276054385121047640320 := by
  rw [← show ((([(7, 1), (11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_7, prime_twentyEightZ_11, prime_twentyEightZ_5573, prime_twentyEightZ_3198253273, prime_twentyEightZ_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124878 : Nat.totient 33103472754879023490318124878 = 9963331525890602505826012800 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (83, 1), (101, 1), (50626684582777451757247, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_13, prime_twentyEightZ_83, prime_twentyEightZ_101, prime_twentyEightZ_50626684582777451757247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124879 : Nat.totient 33103472754879023490318124879 = 33103472754815516616887208184 := by
  rw [← show ((([(521262387533, 1), (63506352168529163, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_521262387533, prime_twentyEightZ_63506352168529163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124880 : Nat.totient 33103472754879023490318124880 = 13219997520015865988509062144 := by
  rw [← show ((([(2, 4), (5, 1), (619, 1), (70908014633, 1), (9427522870043, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_5, prime_twentyEightZ_619, prime_twentyEightZ_70908014633, prime_twentyEightZ_9427522870043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124881 : Nat.totient 33103472754879023490318124881 = 22068742798344623355654848784 := by
  rw [← show ((([(3, 3), (178183, 1), (191599, 1), (35912884381670059, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_178183, prime_twentyEightZ_191599, prime_twentyEightZ_35912884381670059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124882 : Nat.totient 33103472754879023490318124882 = 16043089186760802569167564800 := by
  rw [← show ((([(2, 1), (41, 1), (157, 1), (7993, 1), (239069, 1), (888691, 1), (1514175419, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_41, prime_twentyEightZ_157, prime_twentyEightZ_7993, prime_twentyEightZ_239069, prime_twentyEightZ_888691, prime_twentyEightZ_1514175419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124883 : Nat.totient 33103472754879023490318124883 = 33082786318690500585808576000 := by
  rw [← show ((([(1601, 1), (3414581, 1), (6055427446181247143, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_1601, prime_twentyEightZ_3414581, prime_twentyEightZ_6055427446181247143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124884 : Nat.totient 33103472754879023490318124884 = 9458135072822578140090892800 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_7, prime_twentyEightZ_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124885 : Nat.totient 33103472754879023490318124885 = 24924967721320676510357176320 := by
  rw [← show ((([(5, 1), (17, 1), (389452620645635570474330881, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_5, prime_twentyEightZ_17, prime_twentyEightZ_389452620645635570474330881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124886 : Nat.totient 33103472754879023490318124886 = 16154555405073286883386320168 := by
  rw [← show ((([(2, 1), (43, 1), (1319, 1), (291830251554904380435479, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_43, prime_twentyEightZ_1319, prime_twentyEightZ_291830251554904380435479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124887 : Nat.totient 33103472754879023490318124887 = 21301358906036868126984456192 := by
  rw [← show ((([(3, 1), (29, 1), (3217, 1), (118277801317280051344753, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_29, prime_twentyEightZ_3217, prime_twentyEightZ_118277801317280051344753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124888 : Nat.totient 33103472754879023490318124888 = 15047033070399556131962784000 := by
  rw [← show ((([(2, 3), (11, 1), (376175826759988903299069601, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_11, prime_twentyEightZ_376175826759988903299069601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124889 : Nat.totient 33103472754879023490318124889 = 32799771169971876485819793360 := by
  rw [← show ((([(109, 1), (303701584907147004498331421, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_109, prime_twentyEightZ_303701584907147004498331421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124890 : Nat.totient 33103472754879023490318124890 = 8679545836486682599141781760 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (71, 1), (367, 1), (14115836970606756764153, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_5, prime_twentyEightZ_71, prime_twentyEightZ_367, prime_twentyEightZ_14115836970606756764153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124891 : Nat.totient 33103472754879023490318124891 = 26087409027092615158080900000 := by
  rw [← show ((([(7, 1), (13, 1), (251, 1), (1449300501505145286560051, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_7, prime_twentyEightZ_13, prime_twentyEightZ_251, prime_twentyEightZ_1449300501505145286560051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124892 : Nat.totient 33103472754879023490318124892 = 15825757127512036436651599680 := by
  rw [← show ((([(2, 2), (23, 1), (2939, 1), (16631, 1), (7361524796742341989, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_23, prime_twentyEightZ_2939, prime_twentyEightZ_16631, prime_twentyEightZ_7361524796742341989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124893 : Nat.totient 33103472754879023490318124893 = 21357060547618617027152299200 := by
  rw [← show ((([(3, 1), (31, 1), (1229531, 1), (16698589, 1), (17336896205039, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_31, prime_twentyEightZ_1229531, prime_twentyEightZ_16698589, prime_twentyEightZ_17336896205039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124894 : Nat.totient 33103472754879023490318124894 = 16199571772684746867371444352 := by
  rw [← show ((([(2, 1), (47, 1), (16539367177, 1), (21292507748726713, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_47, prime_twentyEightZ_16539367177, prime_twentyEightZ_21292507748726713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124895 : Nat.totient 33103472754879023490318124895 = 25088060578520333999251100448 := by
  rw [← show ((([(5, 1), (19, 1), (28279, 1), (12322133312567452318279, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_5, prime_twentyEightZ_19, prime_twentyEightZ_28279, prime_twentyEightZ_12322133312567452318279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124896 : Nat.totient 33103472754879023490318124896 = 11034490918293007830106041600 := by
  rw [← show ((([(2, 5), (3, 1), (344827841196656494690813801, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_3, prime_twentyEightZ_344827841196656494690813801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124897 : Nat.totient 33103472754879023490318124897 = 33073185954379590337341769200 := by
  rw [← show ((([(1093, 1), (189484704379, 1), (159837705232951, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_1093, prime_twentyEightZ_189484704379, prime_twentyEightZ_159837705232951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124898 : Nat.totient 33103472754879023490318124898 = 14187057133780802457538392264 := by
  rw [← show ((([(2, 1), (7, 2), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_2, prime_twentyEightZ_7, prime_twentyEightZ_97523, prime_twentyEightZ_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyEightZ_33103472754879023490318124899 : Nat.totient 33103472754879023490318124899 = 19898581264760355523574745600 := by
  rw [← show ((([(3, 2), (11, 1), (127, 1), (4937, 1), (9371, 1), (56909605574267269, 1)] : List FactorBlock).map factorBlockValue).prod) = 33103472754879023490318124899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyEightZ_3, prime_twentyEightZ_11, prime_twentyEightZ_127, prime_twentyEightZ_4937, prime_twentyEightZ_9371, prime_twentyEightZ_56909605574267269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentyEightZ : certifiedKill 1 33103472754879023490318124799 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentyEightZ_33103472754879023490318124800, phi_twentyEightZ_33103472754879023490318124801, phi_twentyEightZ_33103472754879023490318124802,
    phi_twentyEightZ_33103472754879023490318124803, phi_twentyEightZ_33103472754879023490318124804, phi_twentyEightZ_33103472754879023490318124805,
    phi_twentyEightZ_33103472754879023490318124806, phi_twentyEightZ_33103472754879023490318124807, phi_twentyEightZ_33103472754879023490318124808,
    phi_twentyEightZ_33103472754879023490318124809, phi_twentyEightZ_33103472754879023490318124810, phi_twentyEightZ_33103472754879023490318124811,
    phi_twentyEightZ_33103472754879023490318124812, phi_twentyEightZ_33103472754879023490318124813, phi_twentyEightZ_33103472754879023490318124814,
    phi_twentyEightZ_33103472754879023490318124815, phi_twentyEightZ_33103472754879023490318124816, phi_twentyEightZ_33103472754879023490318124817,
    phi_twentyEightZ_33103472754879023490318124818, phi_twentyEightZ_33103472754879023490318124819, phi_twentyEightZ_33103472754879023490318124820,
    phi_twentyEightZ_33103472754879023490318124821, phi_twentyEightZ_33103472754879023490318124822, phi_twentyEightZ_33103472754879023490318124823,
    phi_twentyEightZ_33103472754879023490318124824, phi_twentyEightZ_33103472754879023490318124825, phi_twentyEightZ_33103472754879023490318124826,
    phi_twentyEightZ_33103472754879023490318124827, phi_twentyEightZ_33103472754879023490318124828, phi_twentyEightZ_33103472754879023490318124829,
    phi_twentyEightZ_33103472754879023490318124830, phi_twentyEightZ_33103472754879023490318124831, phi_twentyEightZ_33103472754879023490318124832,
    phi_twentyEightZ_33103472754879023490318124833, phi_twentyEightZ_33103472754879023490318124834, phi_twentyEightZ_33103472754879023490318124835,
    phi_twentyEightZ_33103472754879023490318124836, phi_twentyEightZ_33103472754879023490318124837, phi_twentyEightZ_33103472754879023490318124838,
    phi_twentyEightZ_33103472754879023490318124839, phi_twentyEightZ_33103472754879023490318124840, phi_twentyEightZ_33103472754879023490318124841,
    phi_twentyEightZ_33103472754879023490318124842, phi_twentyEightZ_33103472754879023490318124843, phi_twentyEightZ_33103472754879023490318124844,
    phi_twentyEightZ_33103472754879023490318124845, phi_twentyEightZ_33103472754879023490318124846, phi_twentyEightZ_33103472754879023490318124847,
    phi_twentyEightZ_33103472754879023490318124848, phi_twentyEightZ_33103472754879023490318124849, phi_twentyEightZ_33103472754879023490318124850,
    phi_twentyEightZ_33103472754879023490318124851, phi_twentyEightZ_33103472754879023490318124852, phi_twentyEightZ_33103472754879023490318124853,
    phi_twentyEightZ_33103472754879023490318124854, phi_twentyEightZ_33103472754879023490318124855, phi_twentyEightZ_33103472754879023490318124856,
    phi_twentyEightZ_33103472754879023490318124857, phi_twentyEightZ_33103472754879023490318124858, phi_twentyEightZ_33103472754879023490318124859,
    phi_twentyEightZ_33103472754879023490318124860, phi_twentyEightZ_33103472754879023490318124861, phi_twentyEightZ_33103472754879023490318124862,
    phi_twentyEightZ_33103472754879023490318124863, phi_twentyEightZ_33103472754879023490318124864, phi_twentyEightZ_33103472754879023490318124865,
    phi_twentyEightZ_33103472754879023490318124866, phi_twentyEightZ_33103472754879023490318124867, phi_twentyEightZ_33103472754879023490318124868,
    phi_twentyEightZ_33103472754879023490318124869, phi_twentyEightZ_33103472754879023490318124870, phi_twentyEightZ_33103472754879023490318124871,
    phi_twentyEightZ_33103472754879023490318124872, phi_twentyEightZ_33103472754879023490318124873, phi_twentyEightZ_33103472754879023490318124874,
    phi_twentyEightZ_33103472754879023490318124875, phi_twentyEightZ_33103472754879023490318124876, phi_twentyEightZ_33103472754879023490318124877,
    phi_twentyEightZ_33103472754879023490318124878, phi_twentyEightZ_33103472754879023490318124879, phi_twentyEightZ_33103472754879023490318124880,
    phi_twentyEightZ_33103472754879023490318124881, phi_twentyEightZ_33103472754879023490318124882, phi_twentyEightZ_33103472754879023490318124883,
    phi_twentyEightZ_33103472754879023490318124884, phi_twentyEightZ_33103472754879023490318124885, phi_twentyEightZ_33103472754879023490318124886,
    phi_twentyEightZ_33103472754879023490318124887, phi_twentyEightZ_33103472754879023490318124888, phi_twentyEightZ_33103472754879023490318124889,
    phi_twentyEightZ_33103472754879023490318124890, phi_twentyEightZ_33103472754879023490318124891, phi_twentyEightZ_33103472754879023490318124892,
    phi_twentyEightZ_33103472754879023490318124893, phi_twentyEightZ_33103472754879023490318124894, phi_twentyEightZ_33103472754879023490318124895,
    phi_twentyEightZ_33103472754879023490318124896, phi_twentyEightZ_33103472754879023490318124897, phi_twentyEightZ_33103472754879023490318124898,
    phi_twentyEightZ_33103472754879023490318124899]

end TotientTailPeriodKiller
end Erdos249257
