import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 50P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftyAVFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftyAVFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftyAVFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftyAVFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftyAVFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftyAVFastPow a n * fiftyAVFastPow a n * a
        else fiftyAVFastPow a n * fiftyAVFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftyAV_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftyAV_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftyAV_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftyAV_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftyAV_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftyAV_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftyAV_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftyAV_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftyAV_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftyAV_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftyAV_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftyAV_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftyAV_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftyAV_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftyAV_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftyAV_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftyAV_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftyAV_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftyAV_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftyAV_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftyAV_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftyAV_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftyAV_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftyAV_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftyAV_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftyAV_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftyAV_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftyAV_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftyAV_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftyAV_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftyAV_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftyAV_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftyAV_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftyAV_139 : Nat.Prime 139 := by norm_num
private theorem prime_fiftyAV_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftyAV_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftyAV_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftyAV_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftyAV_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftyAV_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftyAV_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftyAV_193 : Nat.Prime 193 := by norm_num
private theorem prime_fiftyAV_197 : Nat.Prime 197 := by norm_num
private theorem prime_fiftyAV_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftyAV_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftyAV_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftyAV_229 : Nat.Prime 229 := by norm_num
private theorem prime_fiftyAV_233 : Nat.Prime 233 := by norm_num
private theorem prime_fiftyAV_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftyAV_241 : Nat.Prime 241 := by norm_num
private theorem prime_fiftyAV_251 : Nat.Prime 251 := by norm_num
private theorem prime_fiftyAV_269 : Nat.Prime 269 := by norm_num
private theorem prime_fiftyAV_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftyAV_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftyAV_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftyAV_293 : Nat.Prime 293 := by norm_num
private theorem prime_fiftyAV_311 : Nat.Prime 311 := by norm_num
private theorem prime_fiftyAV_317 : Nat.Prime 317 := by norm_num
private theorem prime_fiftyAV_347 : Nat.Prime 347 := by norm_num
private theorem prime_fiftyAV_349 : Nat.Prime 349 := by norm_num
private theorem prime_fiftyAV_359 : Nat.Prime 359 := by norm_num
private theorem prime_fiftyAV_373 : Nat.Prime 373 := by norm_num
private theorem prime_fiftyAV_379 : Nat.Prime 379 := by norm_num
private theorem prime_fiftyAV_383 : Nat.Prime 383 := by norm_num
private theorem prime_fiftyAV_389 : Nat.Prime 389 := by norm_num
private theorem prime_fiftyAV_397 : Nat.Prime 397 := by norm_num
private theorem prime_fiftyAV_401 : Nat.Prime 401 := by norm_num
private theorem prime_fiftyAV_409 : Nat.Prime 409 := by norm_num
private theorem prime_fiftyAV_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftyAV_421 : Nat.Prime 421 := by norm_num
private theorem prime_fiftyAV_439 : Nat.Prime 439 := by norm_num
private theorem prime_fiftyAV_443 : Nat.Prime 443 := by norm_num
private theorem prime_fiftyAV_449 : Nat.Prime 449 := by norm_num
private theorem prime_fiftyAV_463 : Nat.Prime 463 := by norm_num
private theorem prime_fiftyAV_479 : Nat.Prime 479 := by norm_num
private theorem prime_fiftyAV_521 : Nat.Prime 521 := by norm_num
private theorem prime_fiftyAV_541 : Nat.Prime 541 := by norm_num
private theorem prime_fiftyAV_547 : Nat.Prime 547 := by norm_num
private theorem prime_fiftyAV_557 : Nat.Prime 557 := by norm_num
private theorem prime_fiftyAV_569 : Nat.Prime 569 := by norm_num
private theorem prime_fiftyAV_571 : Nat.Prime 571 := by norm_num
private theorem prime_fiftyAV_599 : Nat.Prime 599 := by norm_num
private theorem prime_fiftyAV_601 : Nat.Prime 601 := by norm_num
private theorem prime_fiftyAV_613 : Nat.Prime 613 := by norm_num
private theorem prime_fiftyAV_617 : Nat.Prime 617 := by norm_num
private theorem prime_fiftyAV_619 : Nat.Prime 619 := by norm_num
private theorem prime_fiftyAV_631 : Nat.Prime 631 := by norm_num
private theorem prime_fiftyAV_643 : Nat.Prime 643 := by norm_num
private theorem prime_fiftyAV_673 : Nat.Prime 673 := by norm_num
private theorem prime_fiftyAV_677 : Nat.Prime 677 := by norm_num
private theorem prime_fiftyAV_691 : Nat.Prime 691 := by norm_num
private theorem prime_fiftyAV_701 : Nat.Prime 701 := by norm_num
private theorem prime_fiftyAV_709 : Nat.Prime 709 := by norm_num
private theorem prime_fiftyAV_761 : Nat.Prime 761 := by norm_num
private theorem prime_fiftyAV_811 : Nat.Prime 811 := by norm_num
private theorem prime_fiftyAV_853 : Nat.Prime 853 := by norm_num
private theorem prime_fiftyAV_859 : Nat.Prime 859 := by norm_num
private theorem prime_fiftyAV_883 : Nat.Prime 883 := by norm_num
private theorem prime_fiftyAV_937 : Nat.Prime 937 := by norm_num
private theorem prime_fiftyAV_941 : Nat.Prime 941 := by norm_num
private theorem prime_fiftyAV_947 : Nat.Prime 947 := by norm_num
private theorem prime_fiftyAV_977 : Nat.Prime 977 := by norm_num
private theorem prime_fiftyAV_983 : Nat.Prime 983 := by norm_num
private theorem prime_fiftyAV_997 : Nat.Prime 997 := by norm_num
private theorem prime_fiftyAV_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_fiftyAV_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_fiftyAV_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_fiftyAV_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_fiftyAV_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_fiftyAV_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_fiftyAV_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_fiftyAV_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_fiftyAV_1447 : Nat.Prime 1447 := by norm_num
private theorem prime_fiftyAV_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_fiftyAV_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fiftyAV_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_fiftyAV_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_fiftyAV_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_fiftyAV_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_fiftyAV_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_fiftyAV_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_fiftyAV_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_fiftyAV_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_fiftyAV_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_fiftyAV_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_fiftyAV_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_fiftyAV_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_fiftyAV_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_fiftyAV_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_fiftyAV_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_fiftyAV_2333 : Nat.Prime 2333 := by norm_num
private theorem prime_fiftyAV_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_fiftyAV_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_fiftyAV_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_fiftyAV_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_fiftyAV_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_fiftyAV_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fiftyAV_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_fiftyAV_2707 : Nat.Prime 2707 := by norm_num
private theorem prime_fiftyAV_2833 : Nat.Prime 2833 := by norm_num
private theorem prime_fiftyAV_3019 : Nat.Prime 3019 := by norm_num
private theorem prime_fiftyAV_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_fiftyAV_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_fiftyAV_3331 : Nat.Prime 3331 := by norm_num
private theorem prime_fiftyAV_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_fiftyAV_3571 : Nat.Prime 3571 := by norm_num
private theorem prime_fiftyAV_3677 : Nat.Prime 3677 := by norm_num
private theorem prime_fiftyAV_3911 : Nat.Prime 3911 := by norm_num
private theorem prime_fiftyAV_3943 : Nat.Prime 3943 := by norm_num
private theorem prime_fiftyAV_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_fiftyAV_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_fiftyAV_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_fiftyAV_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_fiftyAV_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_fiftyAV_4157 : Nat.Prime 4157 := by norm_num
private theorem prime_fiftyAV_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_fiftyAV_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_fiftyAV_4357 : Nat.Prime 4357 := by norm_num
private theorem prime_fiftyAV_4483 : Nat.Prime 4483 := by norm_num
private theorem prime_fiftyAV_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_fiftyAV_4999 : Nat.Prime 4999 := by norm_num
private theorem prime_fiftyAV_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fiftyAV_5039 : Nat.Prime 5039 := by norm_num
private theorem prime_fiftyAV_5113 : Nat.Prime 5113 := by norm_num
private theorem prime_fiftyAV_5231 : Nat.Prime 5231 := by norm_num
private theorem prime_fiftyAV_5431 : Nat.Prime 5431 := by norm_num
private theorem prime_fiftyAV_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_fiftyAV_5563 : Nat.Prime 5563 := by norm_num
private theorem prime_fiftyAV_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_fiftyAV_5801 : Nat.Prime 5801 := by norm_num
private theorem prime_fiftyAV_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_fiftyAV_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_fiftyAV_6131 : Nat.Prime 6131 := by norm_num
private theorem prime_fiftyAV_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_fiftyAV_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_fiftyAV_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fiftyAV_6793 : Nat.Prime 6793 := by norm_num
private theorem prime_fiftyAV_6871 : Nat.Prime 6871 := by norm_num
private theorem prime_fiftyAV_7559 : Nat.Prime 7559 := by norm_num
private theorem prime_fiftyAV_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_fiftyAV_8167 : Nat.Prime 8167 := by norm_num
private theorem prime_fiftyAV_8831 : Nat.Prime 8831 := by norm_num
private theorem prime_fiftyAV_9137 : Nat.Prime 9137 := by norm_num
private theorem prime_fiftyAV_9421 : Nat.Prime 9421 := by norm_num
private theorem prime_fiftyAV_9533 : Nat.Prime 9533 := by norm_num
private theorem prime_fiftyAV_10667 : Nat.Prime 10667 := by norm_num
private theorem prime_fiftyAV_10687 : Nat.Prime 10687 := by norm_num
private theorem prime_fiftyAV_11059 : Nat.Prime 11059 := by norm_num
private theorem prime_fiftyAV_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_fiftyAV_12149 : Nat.Prime 12149 := by norm_num
private theorem prime_fiftyAV_12163 : Nat.Prime 12163 := by norm_num
private theorem prime_fiftyAV_12377 : Nat.Prime 12377 := by norm_num
private theorem prime_fiftyAV_12809 : Nat.Prime 12809 := by norm_num
private theorem prime_fiftyAV_12841 : Nat.Prime 12841 := by norm_num
private theorem prime_fiftyAV_13331 : Nat.Prime 13331 := by norm_num
private theorem prime_fiftyAV_13337 : Nat.Prime 13337 := by norm_num
private theorem prime_fiftyAV_14033 : Nat.Prime 14033 := by norm_num
private theorem prime_fiftyAV_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_fiftyAV_14447 : Nat.Prime 14447 := by norm_num
private theorem prime_fiftyAV_14591 : Nat.Prime 14591 := by norm_num
private theorem prime_fiftyAV_15467 : Nat.Prime 15467 := by norm_num
private theorem prime_fiftyAV_16417 : Nat.Prime 16417 := by norm_num
private theorem prime_fiftyAV_16567 : Nat.Prime 16567 := by norm_num
private theorem prime_fiftyAV_17027 : Nat.Prime 17027 := by norm_num
private theorem prime_fiftyAV_17209 : Nat.Prime 17209 := by norm_num
private theorem prime_fiftyAV_17393 : Nat.Prime 17393 := by norm_num
private theorem prime_fiftyAV_18223 : Nat.Prime 18223 := by norm_num
private theorem prime_fiftyAV_19073 : Nat.Prime 19073 := by norm_num
private theorem prime_fiftyAV_19961 : Nat.Prime 19961 := by norm_num
private theorem prime_fiftyAV_20231 : Nat.Prime 20231 := by norm_num
private theorem prime_fiftyAV_20983 : Nat.Prime 20983 := by norm_num
private theorem prime_fiftyAV_21817 : Nat.Prime 21817 := by norm_num
private theorem prime_fiftyAV_22367 : Nat.Prime 22367 := by norm_num
private theorem prime_fiftyAV_22481 : Nat.Prime 22481 := by norm_num
private theorem prime_fiftyAV_22697 : Nat.Prime 22697 := by norm_num
private theorem prime_fiftyAV_23167 : Nat.Prime 23167 := by norm_num
private theorem prime_fiftyAV_23327 : Nat.Prime 23327 := by norm_num
private theorem prime_fiftyAV_25411 : Nat.Prime 25411 := by norm_num
private theorem prime_fiftyAV_26423 : Nat.Prime 26423 := by norm_num
private theorem prime_fiftyAV_26993 : Nat.Prime 26993 := by norm_num
private theorem prime_fiftyAV_30097 : Nat.Prime 30097 := by norm_num
private theorem prime_fiftyAV_30871 : Nat.Prime 30871 := by norm_num
private theorem prime_fiftyAV_31741 : Nat.Prime 31741 := by norm_num
private theorem prime_fiftyAV_32003 : Nat.Prime 32003 := by norm_num
private theorem prime_fiftyAV_32491 : Nat.Prime 32491 := by norm_num
private theorem prime_fiftyAV_32561 : Nat.Prime 32561 := by norm_num
private theorem prime_fiftyAV_33301 : Nat.Prime 33301 := by norm_num
private theorem prime_fiftyAV_34963 : Nat.Prime 34963 := by norm_num
private theorem prime_fiftyAV_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fiftyAV_36013 : Nat.Prime 36013 := by norm_num
private theorem prime_fiftyAV_36383 : Nat.Prime 36383 := by norm_num
private theorem prime_fiftyAV_36997 : Nat.Prime 36997 := by norm_num
private theorem prime_fiftyAV_37039 : Nat.Prime 37039 := by norm_num
private theorem prime_fiftyAV_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fiftyAV_40543 : Nat.Prime 40543 := by norm_num
private theorem prime_fiftyAV_41467 : Nat.Prime 41467 := by norm_num
private theorem prime_fiftyAV_42337 : Nat.Prime 42337 := by norm_num
private theorem prime_fiftyAV_42379 : Nat.Prime 42379 := by norm_num
private theorem prime_fiftyAV_42943 : Nat.Prime 42943 := by norm_num
private theorem prime_fiftyAV_43669 : Nat.Prime 43669 := by norm_num
private theorem prime_fiftyAV_45697 : Nat.Prime 45697 := by norm_num
private theorem prime_fiftyAV_46219 : Nat.Prime 46219 := by norm_num
private theorem prime_fiftyAV_47431 : Nat.Prime 47431 := by norm_num
private theorem prime_fiftyAV_49009 : Nat.Prime 49009 := by norm_num
private theorem prime_fiftyAV_49117 : Nat.Prime 49117 := by norm_num
private theorem prime_fiftyAV_53951 : Nat.Prime 53951 := by norm_num
private theorem prime_fiftyAV_54421 : Nat.Prime 54421 := by norm_num
private theorem prime_fiftyAV_58789 : Nat.Prime 58789 := by norm_num
private theorem prime_fiftyAV_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fiftyAV_65423 : Nat.Prime 65423 := by norm_num
private theorem prime_fiftyAV_66533 : Nat.Prime 66533 := by norm_num
private theorem prime_fiftyAV_68897 : Nat.Prime 68897 := by norm_num
private theorem prime_fiftyAV_70249 : Nat.Prime 70249 := by norm_num
private theorem prime_fiftyAV_74929 : Nat.Prime 74929 := by norm_num
private theorem prime_fiftyAV_78041 : Nat.Prime 78041 := by norm_num
private theorem prime_fiftyAV_80687 : Nat.Prime 80687 := by norm_num
private theorem prime_fiftyAV_85303 : Nat.Prime 85303 := by norm_num
private theorem prime_fiftyAV_90353 : Nat.Prime 90353 := by norm_num
private theorem prime_fiftyAV_94421 : Nat.Prime 94421 := by norm_num
private theorem prime_fiftyAV_95561 : Nat.Prime 95561 := by norm_num
private theorem prime_fiftyAV_96443 : Nat.Prime 96443 := by norm_num
private theorem prime_fiftyAV_97387 : Nat.Prime 97387 := by norm_num
private theorem prime_fiftyAV_98887 : Nat.Prime 98887 := by norm_num
private theorem prime_fiftyAV_99347 : Nat.Prime 99347 := by norm_num
private theorem prime_fiftyAV_101287 : Nat.Prime 101287 := by norm_num
private theorem prime_fiftyAV_101501 : Nat.Prime 101501 := by norm_num
private theorem prime_fiftyAV_102161 : Nat.Prime 102161 := by norm_num
private theorem prime_fiftyAV_104003 : Nat.Prime 104003 := by norm_num
private theorem prime_fiftyAV_104527 : Nat.Prime 104527 := by norm_num
private theorem prime_fiftyAV_109829 : Nat.Prime 109829 := by norm_num
private theorem prime_fiftyAV_114859 : Nat.Prime 114859 := by norm_num
private theorem prime_fiftyAV_115327 : Nat.Prime 115327 := by norm_num
private theorem prime_fiftyAV_116687 : Nat.Prime 116687 := by norm_num
private theorem prime_fiftyAV_121591 : Nat.Prime 121591 := by norm_num
private theorem prime_fiftyAV_127727 : Nat.Prime 127727 := by norm_num
private theorem prime_fiftyAV_129457 : Nat.Prime 129457 := by norm_num
private theorem prime_fiftyAV_132929 : Nat.Prime 132929 := by norm_num
private theorem prime_fiftyAV_143669 : Nat.Prime 143669 := by norm_num
private theorem prime_fiftyAV_143687 : Nat.Prime 143687 := by norm_num
private theorem prime_fiftyAV_152671 : Nat.Prime 152671 := by norm_num
private theorem prime_fiftyAV_156539 : Nat.Prime 156539 := by norm_num
private theorem prime_fiftyAV_159521 : Nat.Prime 159521 := by norm_num
private theorem prime_fiftyAV_160423 : Nat.Prime 160423 := by norm_num
private theorem prime_fiftyAV_179999 : Nat.Prime 179999 := by norm_num
private theorem prime_fiftyAV_190843 : Nat.Prime 190843 := by norm_num
private theorem prime_fiftyAV_196453 : Nat.Prime 196453 := by norm_num
private theorem prime_fiftyAV_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_fiftyAV_211441 : Nat.Prime 211441 := by norm_num
private theorem prime_fiftyAV_223381 : Nat.Prime 223381 := by norm_num
private theorem prime_fiftyAV_223469 : Nat.Prime 223469 := by norm_num
private theorem prime_fiftyAV_232411 : Nat.Prime 232411 := by norm_num
private theorem prime_fiftyAV_242819 : Nat.Prime 242819 := by norm_num
private theorem prime_fiftyAV_252401 : Nat.Prime 252401 := by norm_num
private theorem prime_fiftyAV_254197 : Nat.Prime 254197 := by norm_num
private theorem prime_fiftyAV_259949 : Nat.Prime 259949 := by norm_num
private theorem prime_fiftyAV_272329 : Nat.Prime 272329 := by norm_num
private theorem prime_fiftyAV_274121 : Nat.Prime 274121 := by norm_num
private theorem prime_fiftyAV_277747 : Nat.Prime 277747 := by norm_num
private theorem prime_fiftyAV_295219 : Nat.Prime 295219 := by norm_num
private theorem prime_fiftyAV_332309 : Nat.Prime 332309 := by norm_num
private theorem prime_fiftyAV_354169 : Nat.Prime 354169 := by norm_num
private theorem prime_fiftyAV_374681 : Nat.Prime 374681 := by norm_num
private theorem prime_fiftyAV_375121 : Nat.Prime 375121 := by norm_num
private theorem prime_fiftyAV_381559 : Nat.Prime 381559 := by norm_num
private theorem prime_fiftyAV_384497 : Nat.Prime 384497 := by norm_num
private theorem prime_fiftyAV_396733 : Nat.Prime 396733 := by norm_num
private theorem prime_fiftyAV_401417 : Nat.Prime 401417 := by norm_num
private theorem prime_fiftyAV_412567 : Nat.Prime 412567 := by norm_num
private theorem prime_fiftyAV_446389 : Nat.Prime 446389 := by norm_num
private theorem prime_fiftyAV_508367 : Nat.Prime 508367 := by norm_num
private theorem prime_fiftyAV_512503 : Nat.Prime 512503 := by norm_num
private theorem prime_fiftyAV_512713 : Nat.Prime 512713 := by norm_num
private theorem prime_fiftyAV_517177 : Nat.Prime 517177 := by norm_num
private theorem prime_fiftyAV_537637 : Nat.Prime 537637 := by norm_num
private theorem prime_fiftyAV_558757 : Nat.Prime 558757 := by norm_num
private theorem prime_fiftyAV_583351 : Nat.Prime 583351 := by norm_num
private theorem prime_fiftyAV_589507 : Nat.Prime 589507 := by norm_num
private theorem prime_fiftyAV_621799 : Nat.Prime 621799 := by norm_num
private theorem prime_fiftyAV_625199 : Nat.Prime 625199 := by norm_num
private theorem prime_fiftyAV_656951 : Nat.Prime 656951 := by norm_num
private theorem prime_fiftyAV_698039 : Nat.Prime 698039 := by norm_num
private theorem prime_fiftyAV_842587 : Nat.Prime 842587 := by norm_num
private theorem prime_fiftyAV_868397 : Nat.Prime 868397 := by norm_num
private theorem prime_fiftyAV_906371 : Nat.Prime 906371 := by norm_num
private theorem prime_fiftyAV_939487 : Nat.Prime 939487 := by norm_num
private theorem prime_fiftyAV_1044397 : Nat.Prime 1044397 := by norm_num
private theorem prime_fiftyAV_1109609 : Nat.Prime 1109609 := by norm_num
private theorem prime_fiftyAV_1120081 : Nat.Prime 1120081 := by norm_num
private theorem prime_fiftyAV_1120363 : Nat.Prime 1120363 := by norm_num
private theorem prime_fiftyAV_1171811 : Nat.Prime 1171811 := by norm_num
private theorem prime_fiftyAV_1194671 : Nat.Prime 1194671 := by norm_num
private theorem prime_fiftyAV_1273889 : Nat.Prime 1273889 := by norm_num
private theorem prime_fiftyAV_1292237 : Nat.Prime 1292237 := by norm_num
private theorem prime_fiftyAV_1348073 : Nat.Prime 1348073 := by norm_num
private theorem prime_fiftyAV_1433741 : Nat.Prime 1433741 := by norm_num
private theorem prime_fiftyAV_1467937 : Nat.Prime 1467937 := by norm_num
private theorem prime_fiftyAV_1544987 : Nat.Prime 1544987 := by norm_num
private theorem prime_fiftyAV_1681363 : Nat.Prime 1681363 := by norm_num
private theorem prime_fiftyAV_1791037 : Nat.Prime 1791037 := by norm_num
private theorem prime_fiftyAV_1803947 : Nat.Prime 1803947 := by norm_num
private theorem prime_fiftyAV_2003917 : Nat.Prime 2003917 := by norm_num
private theorem prime_fiftyAV_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_fiftyAV_2227409 : Nat.Prime 2227409 := by norm_num
private theorem prime_fiftyAV_2306261 : Nat.Prime 2306261 := by norm_num
private theorem prime_fiftyAV_2409709 : Nat.Prime 2409709 := by norm_num
private theorem prime_fiftyAV_2428859 : Nat.Prime 2428859 := by norm_num
private theorem prime_fiftyAV_2438833 : Nat.Prime 2438833 := by norm_num
private theorem prime_fiftyAV_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_fiftyAV_2596889 : Nat.Prime 2596889 := by norm_num
private theorem prime_fiftyAV_2669767 : Nat.Prime 2669767 := by norm_num
private theorem prime_fiftyAV_3439229 : Nat.Prime 3439229 := by norm_num
private theorem prime_fiftyAV_3470647 : Nat.Prime 3470647 := by norm_num
private theorem prime_fiftyAV_3509741 : Nat.Prime 3509741 := by norm_num
private theorem prime_fiftyAV_3534683 : Nat.Prime 3534683 := by norm_num
private theorem prime_fiftyAV_3539743 : Nat.Prime 3539743 := by norm_num
private theorem prime_fiftyAV_3558407 : Nat.Prime 3558407 := by norm_num
private theorem prime_fiftyAV_3834547 : Nat.Prime 3834547 := by norm_num
private theorem prime_fiftyAV_3843031 : Nat.Prime 3843031 := by norm_num
private theorem prime_fiftyAV_3969583 : Nat.Prime 3969583 := by norm_num
private theorem prime_fiftyAV_4092997 : Nat.Prime 4092997 := by norm_num
private theorem prime_fiftyAV_4247039 : Nat.Prime 4247039 := by norm_num
private theorem prime_fiftyAV_4719079 : Nat.Prime 4719079 := by norm_num
private theorem prime_fiftyAV_4801033 : Nat.Prime 4801033 := by norm_num
private theorem prime_fiftyAV_5358737 : Nat.Prime 5358737 := by norm_num
private theorem prime_fiftyAV_5416363 : Nat.Prime 5416363 := by norm_num
private theorem prime_fiftyAV_5500067 : Nat.Prime 5500067 := by norm_num
private theorem prime_fiftyAV_5592011 : Nat.Prime 5592011 := by norm_num
private theorem prime_fiftyAV_5858417 : Nat.Prime 5858417 := by norm_num
private theorem prime_fiftyAV_6952579 : Nat.Prime 6952579 := by norm_num
private theorem prime_fiftyAV_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fiftyAV_7268321 : Nat.Prime 7268321 := by norm_num
private theorem prime_fiftyAV_7599481 : Nat.Prime 7599481 := by norm_num
private theorem prime_fiftyAV_7929133 : Nat.Prime 7929133 := by norm_num
private theorem prime_fiftyAV_8027563 : Nat.Prime 8027563 := by norm_num
private theorem prime_fiftyAV_8408039 : Nat.Prime 8408039 := by norm_num
private theorem prime_fiftyAV_8590367 : Nat.Prime 8590367 := by norm_num
private theorem prime_fiftyAV_8903891 : Nat.Prime 8903891 := by norm_num
private theorem prime_fiftyAV_9456049 : Nat.Prime 9456049 := by norm_num
private theorem prime_fiftyAV_9813829 : Nat.Prime 9813829 := by norm_num
private theorem prime_fiftyAV_9939247 : Nat.Prime 9939247 := by norm_num
private theorem prime_fiftyAV_10126309 : Nat.Prime 10126309 := by norm_num
private theorem prime_fiftyAV_11637001 : Nat.Prime 11637001 := by norm_num
private theorem prime_fiftyAV_12128443 : Nat.Prime 12128443 := by norm_num
private theorem prime_fiftyAV_13510961 : Nat.Prime 13510961 := by norm_num
private theorem prime_fiftyAV_13737811 : Nat.Prime 13737811 := by norm_num
private theorem prime_fiftyAV_14142311 : Nat.Prime 14142311 := by norm_num
private theorem prime_fiftyAV_14375651 : Nat.Prime 14375651 := by norm_num
private theorem prime_fiftyAV_14588891 : Nat.Prime 14588891 := by norm_num
private theorem prime_fiftyAV_15558227 : Nat.Prime 15558227 := by norm_num
private theorem prime_fiftyAV_16230497 : Nat.Prime 16230497 := by norm_num
private theorem prime_fiftyAV_16937033 : Nat.Prime 16937033 := by norm_num
private theorem prime_fiftyAV_17365121 : Nat.Prime 17365121 := by norm_num
private theorem prime_fiftyAV_21268679 : Nat.Prime 21268679 := by norm_num
private theorem prime_fiftyAV_21421693 : Nat.Prime 21421693 := by norm_num
private theorem prime_fiftyAV_23704693 : Nat.Prime 23704693 := by norm_num
private theorem prime_fiftyAV_27212041 : Nat.Prime 27212041 := by norm_num
private theorem prime_fiftyAV_29654903 : Nat.Prime 29654903 := by norm_num
private theorem prime_fiftyAV_31448647 : Nat.Prime 31448647 := by
  apply lucas_primality 31448647 (3 : ZMod 31448647)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (13337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (13337, 1)] : List FactorBlock).map factorBlockValue).prod) = 31448647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_131
      · exact prime_fiftyAV_13337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31448647) ^ 15724323 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 31448647) ^ 10482882 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 31448647) ^ 240066 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 31448647) ^ 2358 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_32364193 : Nat.Prime 32364193 := by
  apply lucas_primality 32364193 (15 : ZMod 32364193)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (17, 1), (2833, 1)] : List FactorBlock).map factorBlockValue).prod) = 32364193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_2833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 32364193) ^ 16182096 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 10788064 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 4623456 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 1903776 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (15 : ZMod 32364193) ^ 11424 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_33064529 : Nat.Prime 33064529 := by
  apply lucas_primality 33064529 (3 : ZMod 33064529)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (295219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (295219, 1)] : List FactorBlock).map factorBlockValue).prod) = 33064529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_295219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33064529) ^ 16532264 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33064529) ^ 4723504 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33064529) ^ 112 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_33099329 : Nat.Prime 33099329 := by
  apply lucas_primality 33099329 (3 : ZMod 33099329)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (517177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (517177, 1)] : List FactorBlock).map factorBlockValue).prod) = 33099329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_517177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 33099329) ^ 16549664 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33099329) ^ 64 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_33610891 : Nat.Prime 33610891 := by
  apply lucas_primality 33610891 (12 : ZMod 33610891)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1120363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1120363, 1)] : List FactorBlock).map factorBlockValue).prod) = 33610891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_1120363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 33610891) ^ 16805445 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (12 : ZMod 33610891) ^ 11203630 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (12 : ZMod 33610891) ^ 6722178 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (12 : ZMod 33610891) ^ 30 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_34996123 : Nat.Prime 34996123 := by
  apply lucas_primality 34996123 (3 : ZMod 34996123)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (277747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (277747, 1)] : List FactorBlock).map factorBlockValue).prod) = 34996123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_277747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34996123) ^ 17498061 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 34996123) ^ 11665374 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 34996123) ^ 4999446 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 34996123) ^ 126 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_38421533 : Nat.Prime 38421533 := by
  apply lucas_primality 38421533 (2 : ZMod 38421533)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (223381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (223381, 1)] : List FactorBlock).map factorBlockValue).prod) = 38421533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_223381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38421533) ^ 19210766 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 38421533) ^ 893524 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 38421533) ^ 172 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_42416197 : Nat.Prime 42416197 := by
  apply lucas_primality 42416197 (2 : ZMod 42416197)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3534683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3534683, 1)] : List FactorBlock).map factorBlockValue).prod) = 42416197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_3534683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42416197) ^ 21208098 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 42416197) ^ 14138732 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 42416197) ^ 12 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_42716273 : Nat.Prime 42716273 := by
  apply lucas_primality 42716273 (3 : ZMod 42716273)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2669767, 1)] : List FactorBlock).map factorBlockValue).prod) = 42716273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_2669767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 42716273) ^ 21358136 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 42716273) ^ 16 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_45503099 : Nat.Prime 45503099 := by
  apply lucas_primality 45503099 (2 : ZMod 45503099)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (521, 1), (43669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (521, 1), (43669, 1)] : List FactorBlock).map factorBlockValue).prod) = 45503099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_521
      · exact prime_fiftyAV_43669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45503099) ^ 22751549 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 45503099) ^ 87338 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 45503099) ^ 1042 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_48244037 : Nat.Prime 48244037 := by
  apply lucas_primality 48244037 (2 : ZMod 48244037)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (152671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (152671, 1)] : List FactorBlock).map factorBlockValue).prod) = 48244037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_152671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 48244037) ^ 24122018 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 48244037) ^ 610684 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 48244037) ^ 316 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_50536133 : Nat.Prime 50536133 := by
  apply lucas_primality 50536133 (2 : ZMod 50536133)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (96443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (96443, 1)] : List FactorBlock).map factorBlockValue).prod) = 50536133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_131
      · exact prime_fiftyAV_96443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50536133) ^ 25268066 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50536133) ^ 385772 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50536133) ^ 524 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_50906021 : Nat.Prime 50906021 := by
  apply lucas_primality 50906021 (2 : ZMod 50906021)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (29, 1), (79, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (29, 1), (79, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) = 50906021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50906021) ^ 25453010 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50906021) ^ 10181204 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50906021) ^ 4627820 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50906021) ^ 1755380 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50906021) ^ 644380 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50906021) ^ 504020 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_56492851 : Nat.Prime 56492851 := by
  apply lucas_primality 56492851 (3 : ZMod 56492851)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31, 1), (12149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31, 1), (12149, 1)] : List FactorBlock).map factorBlockValue).prod) = 56492851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_12149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56492851) ^ 28246425 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 56492851) ^ 18830950 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 56492851) ^ 11298570 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 56492851) ^ 1822350 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 56492851) ^ 4650 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_57732893 : Nat.Prime 57732893 := by
  apply lucas_primality 57732893 (2 : ZMod 57732893)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (619, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (619, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) = 57732893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_619
      · exact prime_fiftyAV_3331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57732893) ^ 28866446 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57732893) ^ 8247556 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57732893) ^ 93268 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57732893) ^ 17332 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_62075323 : Nat.Prime 62075323 := by
  apply lucas_primality 62075323 (2 : ZMod 62075323)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (127727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (127727, 1)] : List FactorBlock).map factorBlockValue).prod) = 62075323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_127727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 62075323) ^ 31037661 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 62075323) ^ 20691774 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 62075323) ^ 486 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_68784581 : Nat.Prime 68784581 := by
  apply lucas_primality 68784581 (3 : ZMod 68784581)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 68784581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68784581) ^ 34392290 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 13756916 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 68784581) ^ 20 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_80523799 : Nat.Prime 80523799 := by
  apply lucas_primality 80523799 (3 : ZMod 80523799)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (71, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (71, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod) = 80523799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_71
      · exact prime_fiftyAV_11119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 80523799) ^ 40261899 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 80523799) ^ 26841266 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 80523799) ^ 4736694 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 80523799) ^ 1134138 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 80523799) ^ 7242 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_80750533 : Nat.Prime 80750533 := by
  apply lucas_primality 80750533 (2 : ZMod 80750533)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (354169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (354169, 1)] : List FactorBlock).map factorBlockValue).prod) = 80750533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_354169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80750533) ^ 40375266 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 80750533) ^ 26916844 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 80750533) ^ 4250028 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 80750533) ^ 228 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_86253907 : Nat.Prime 86253907 := by
  apply lucas_primality 86253907 (2 : ZMod 86253907)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14375651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14375651, 1)] : List FactorBlock).map factorBlockValue).prod) = 86253907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_14375651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86253907) ^ 43126953 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 86253907) ^ 28751302 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 86253907) ^ 6 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_97654321 : Nat.Prime 97654321 := by
  apply lucas_primality 97654321 (17 : ZMod 97654321)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 97654321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 97654321) ^ 48827160 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 32551440 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 19530864 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 4245840 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 97654321) ^ 16560 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_104190727 : Nat.Prime 104190727 := by
  apply lucas_primality 104190727 (3 : ZMod 104190727)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17365121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17365121, 1)] : List FactorBlock).map factorBlockValue).prod) = 104190727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_17365121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 104190727) ^ 52095363 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 104190727) ^ 34730242 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 104190727) ^ 6 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_105602689 : Nat.Prime 105602689 := by
  apply lucas_primality 105602689 (21 : ZMod 105602689)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (29, 2), (109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (29, 2), (109, 1)] : List FactorBlock).map factorBlockValue).prod) = 105602689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 105602689) ^ 52801344 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (21 : ZMod 105602689) ^ 35200896 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (21 : ZMod 105602689) ^ 3641472 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (21 : ZMod 105602689) ^ 968832 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_106163831 : Nat.Prime 106163831 := by
  apply lucas_primality 106163831 (11 : ZMod 106163831)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (558757, 1)] : List FactorBlock).map factorBlockValue).prod) = 106163831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_558757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106163831) ^ 53081915 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 21232766 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 5587570 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 106163831) ^ 190 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_129334193 : Nat.Prime 129334193 := by
  apply lucas_primality 129334193 (3 : ZMod 129334193)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (621799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (621799, 1)] : List FactorBlock).map factorBlockValue).prod) = 129334193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_621799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 129334193) ^ 64667096 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 129334193) ^ 9948784 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 129334193) ^ 208 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_135170359 : Nat.Prime 135170359 := by
  apply lucas_primality 135170359 (6 : ZMod 135170359)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (163, 1), (3371, 1)] : List FactorBlock).map factorBlockValue).prod) = 135170359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_163
      · exact prime_fiftyAV_3371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 135170359) ^ 67585179 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 45056786 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 3296838 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 829266 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 135170359) ^ 40098 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_149650877 : Nat.Prime 149650877 := by
  apply lucas_primality 149650877 (2 : ZMod 149650877)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (512503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (512503, 1)] : List FactorBlock).map factorBlockValue).prod) = 149650877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_73
      · exact prime_fiftyAV_512503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 149650877) ^ 74825438 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 149650877) ^ 2050012 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 149650877) ^ 292 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_152559443 : Nat.Prime 152559443 := by
  apply lucas_primality 152559443 (5 : ZMod 152559443)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (41, 1), (43, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (41, 1), (43, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 152559443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 152559443) ^ 76279721 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 152559443) ^ 21794206 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 152559443) ^ 3720962 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 152559443) ^ 3547894 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 152559443) ^ 172774 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_163646341 : Nat.Prime 163646341 := by
  apply lucas_primality 163646341 (7 : ZMod 163646341)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (19073, 1)] : List FactorBlock).map factorBlockValue).prod) = 163646341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_19073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 163646341) ^ 81823170 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 54548780 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 32729268 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 14876940 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 12588180 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 163646341) ^ 8580 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_167470561 : Nat.Prime 167470561 := by
  apply lucas_primality 167470561 (13 : ZMod 167470561)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (19, 1), (6121, 1)] : List FactorBlock).map factorBlockValue).prod) = 167470561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_6121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 167470561) ^ 83735280 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 55823520 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 33494112 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 8814240 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 167470561) ^ 27360 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_222452891 : Nat.Prime 222452891 := by
  apply lucas_primality 222452891 (2 : ZMod 222452891)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (229, 1), (8831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (229, 1), (8831, 1)] : List FactorBlock).map factorBlockValue).prod) = 222452891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_229
      · exact prime_fiftyAV_8831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 222452891) ^ 111226445 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 222452891) ^ 44490578 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 222452891) ^ 20222990 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 222452891) ^ 971410 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 222452891) ^ 25190 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_191
      · exact prime_fiftyAV_383
      · exact prime_fiftyAV_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_247836439 : Nat.Prime 247836439 := by
  apply lucas_primality 247836439 (3 : ZMod 247836439)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (379, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (379, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) = 247836439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_379
      · exact prime_fiftyAV_2137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 247836439) ^ 123918219 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 247836439) ^ 82612146 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 247836439) ^ 14578614 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 247836439) ^ 653922 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 247836439) ^ 115974 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_248528221 : Nat.Prime 248528221 := by
  apply lucas_primality 248528221 (10 : ZMod 248528221)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1747, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1747, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) = 248528221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_1747
      · exact prime_fiftyAV_2371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 248528221) ^ 124264110 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 248528221) ^ 82842740 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 248528221) ^ 49705644 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 248528221) ^ 142260 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 248528221) ^ 104820 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_248944687 : Nat.Prime 248944687 := by
  apply lucas_primality 248944687 (3 : ZMod 248944687)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1803947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1803947, 1)] : List FactorBlock).map factorBlockValue).prod) = 248944687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_1803947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 248944687) ^ 124472343 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 248944687) ^ 82981562 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 248944687) ^ 10823682 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 248944687) ^ 138 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_266338661 : Nat.Prime 266338661 := by
  apply lucas_primality 266338661 (10 : ZMod 266338661)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (17, 1), (47, 1), (2381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (17, 1), (47, 1), (2381, 1)] : List FactorBlock).map factorBlockValue).prod) = 266338661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_2381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 266338661) ^ 133169330 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 53267732 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 38048380 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 15666980 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 5666780 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 266338661) ^ 111860 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_269471693 : Nat.Prime 269471693 := by
  apply lucas_primality 269471693 (2 : ZMod 269471693)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 2), (33301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 2), (33301, 1)] : List FactorBlock).map factorBlockValue).prod) = 269471693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_33301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 269471693) ^ 134735846 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 269471693) ^ 38495956 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 269471693) ^ 15851276 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 269471693) ^ 8092 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_351304411 : Nat.Prime 351304411 := by
  apply lucas_primality 351304411 (2 : ZMod 351304411)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (272329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (272329, 1)] : List FactorBlock).map factorBlockValue).prod) = 351304411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_272329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 351304411) ^ 175652205 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 351304411) ^ 117101470 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 351304411) ^ 70260882 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 351304411) ^ 8169870 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 351304411) ^ 1290 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_410133851 : Nat.Prime 410133851 := by
  apply lucas_primality 410133851 (2 : ZMod 410133851)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1171811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1171811, 1)] : List FactorBlock).map factorBlockValue).prod) = 410133851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_1171811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 410133851) ^ 205066925 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 410133851) ^ 82026770 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 410133851) ^ 58590550 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 410133851) ^ 350 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_413396887 : Nat.Prime 413396887 := by
  apply lucas_primality 413396887 (3 : ZMod 413396887)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (103, 1), (95561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (103, 1), (95561, 1)] : List FactorBlock).map factorBlockValue).prod) = 413396887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_103
      · exact prime_fiftyAV_95561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 413396887) ^ 206698443 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 413396887) ^ 137798962 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 413396887) ^ 59056698 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 413396887) ^ 4013562 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 413396887) ^ 4326 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_414430283 : Nat.Prime 414430283 := by
  apply lucas_primality 414430283 (2 : ZMod 414430283)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1483, 1), (19961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1483, 1), (19961, 1)] : List FactorBlock).map factorBlockValue).prod) = 414430283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_1483
      · exact prime_fiftyAV_19961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 414430283) ^ 207215141 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 414430283) ^ 59204326 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 414430283) ^ 279454 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 414430283) ^ 20762 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_416413469 : Nat.Prime 416413469 := by
  apply lucas_primality 416413469 (2 : ZMod 416413469)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1511, 1), (68897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1511, 1), (68897, 1)] : List FactorBlock).map factorBlockValue).prod) = 416413469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_1511
      · exact prime_fiftyAV_68897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 416413469) ^ 208206734 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 416413469) ^ 275588 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 416413469) ^ 6044 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_422410757 : Nat.Prime 422410757 := by
  apply lucas_primality 422410757 (2 : ZMod 422410757)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (105602689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (105602689, 1)] : List FactorBlock).map factorBlockValue).prod) = 422410757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_105602689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 422410757) ^ 211205378 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 422410757) ^ 4 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_438217711 : Nat.Prime 438217711 := by
  apply lucas_primality 438217711 (14 : ZMod 438217711)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (109829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (109829, 1)] : List FactorBlock).map factorBlockValue).prod) = 438217711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_109829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 438217711) ^ 219108855 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 146072570 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 87643542 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 62602530 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 23064090 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 438217711) ^ 3990 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_515717623 : Nat.Prime 515717623 := by
  apply lucas_primality 515717623 (6 : ZMod 515717623)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (4092997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (4092997, 1)] : List FactorBlock).map factorBlockValue).prod) = 515717623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_4092997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 515717623) ^ 257858811 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 515717623) ^ 171905874 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 515717623) ^ 73673946 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 515717623) ^ 126 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_621772253 : Nat.Prime 621772253 := by
  apply lucas_primality 621772253 (2 : ZMod 621772253)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (868397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (868397, 1)] : List FactorBlock).map factorBlockValue).prod) = 621772253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_179
      · exact prime_fiftyAV_868397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 621772253) ^ 310886126 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 621772253) ^ 3473588 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 621772253) ^ 716 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_624578257 : Nat.Prime 624578257 := by
  apply lucas_primality 624578257 (15 : ZMod 624578257)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (41, 1), (179, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (41, 1), (179, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) = 624578257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_179
      · exact prime_fiftyAV_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 624578257) ^ 312289128 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (15 : ZMod 624578257) ^ 208192752 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (15 : ZMod 624578257) ^ 15233616 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (15 : ZMod 624578257) ^ 3489264 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (15 : ZMod 624578257) ^ 3170448 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_675548051 : Nat.Prime 675548051 := by
  apply lucas_primality 675548051 (2 : ZMod 675548051)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13510961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13510961, 1)] : List FactorBlock).map factorBlockValue).prod) = 675548051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_13510961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 675548051) ^ 337774025 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 675548051) ^ 135109610 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 675548051) ^ 50 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_756314467 : Nat.Prime 756314467 := by
  apply lucas_primality 756314467 (2 : ZMod 756314467)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1093, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1093, 1), (115327, 1)] : List FactorBlock).map factorBlockValue).prod) = 756314467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_1093
      · exact prime_fiftyAV_115327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 756314467) ^ 378157233 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 756314467) ^ 252104822 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 756314467) ^ 691962 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 756314467) ^ 6558 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_810371591 : Nat.Prime 810371591 := by
  apply lucas_primality 810371591 (14 : ZMod 810371591)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (53, 1), (113, 1), (1933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (53, 1), (113, 1), (1933, 1)] : List FactorBlock).map factorBlockValue).prod) = 810371591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_113
      · exact prime_fiftyAV_1933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 810371591) ^ 405185795 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 810371591) ^ 162074318 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 810371591) ^ 115767370 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 810371591) ^ 15290030 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 810371591) ^ 7171430 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 810371591) ^ 419230 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_820267703 : Nat.Prime 820267703 := by
  apply lucas_primality 820267703 (5 : ZMod 820267703)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (410133851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (410133851, 1)] : List FactorBlock).map factorBlockValue).prod) = 820267703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_410133851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 820267703) ^ 410133851 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 820267703) ^ 2 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_840144259 : Nat.Prime 840144259 := by
  apply lucas_primality 840144259 (2 : ZMod 840144259)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (15558227, 1)] : List FactorBlock).map factorBlockValue).prod) = 840144259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_15558227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 840144259) ^ 420072129 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 280048086 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 840144259) ^ 54 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_889647091 : Nat.Prime 889647091 := by
  apply lucas_primality 889647091 (3 : ZMod 889647091)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29654903, 1)] : List FactorBlock).map factorBlockValue).prod) = 889647091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_29654903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 889647091) ^ 444823545 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 296549030 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 177929418 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 889647091) ^ 30 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1000334917 : Nat.Prime 1000334917 := by
  apply lucas_primality 1000334917 (5 : ZMod 1000334917)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (3969583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (3969583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1000334917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_3969583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1000334917) ^ 500167458 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1000334917) ^ 333444972 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1000334917) ^ 142904988 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1000334917) ^ 252 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1100273971 : Nat.Prime 1100273971 := by
  apply lucas_primality 1100273971 (3 : ZMod 1100273971)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (359, 1), (102161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (359, 1), (102161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1100273971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_359
      · exact prime_fiftyAV_102161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1100273971) ^ 550136985 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100273971) ^ 366757990 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100273971) ^ 220054794 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100273971) ^ 3064830 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100273971) ^ 10770 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_113
      · exact prime_fiftyAV_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1246529923 : Nat.Prime 1246529923 := by
  apply lucas_primality 1246529923 (2 : ZMod 1246529923)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (569, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (569, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1246529923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_569
      · exact prime_fiftyAV_1747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1246529923) ^ 623264961 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 415509974 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 113320902 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 65606838 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 2190738 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246529923) ^ 713526 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1334422357 : Nat.Prime 1334422357 := by
  apply lucas_primality 1334422357 (5 : ZMod 1334422357)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (3834547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (3834547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1334422357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_3834547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1334422357) ^ 667211178 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334422357) ^ 444807452 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334422357) ^ 46014564 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334422357) ^ 348 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1421721311 : Nat.Prime 1421721311 := by
  apply lucas_primality 1421721311 (17 : ZMod 1421721311)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (229, 1), (26993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (229, 1), (26993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1421721311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_229
      · exact prime_fiftyAV_26993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1421721311) ^ 710860655 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1421721311) ^ 284344262 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1421721311) ^ 61813970 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1421721311) ^ 6208390 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1421721311) ^ 52670 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1724446379 : Nat.Prime 1724446379 := by
  apply lucas_primality 1724446379 (2 : ZMod 1724446379)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (557, 1), (17393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (557, 1), (17393, 1)] : List FactorBlock).map factorBlockValue).prod) = 1724446379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_89
      · exact prime_fiftyAV_557
      · exact prime_fiftyAV_17393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1724446379) ^ 862223189 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724446379) ^ 19375802 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724446379) ^ 3095954 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724446379) ^ 99146 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1868119619 : Nat.Prime 1868119619 := by
  apply lucas_primality 1868119619 (2 : ZMod 1868119619)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4019, 1), (232411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4019, 1), (232411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1868119619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_4019
      · exact prime_fiftyAV_232411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1868119619) ^ 934059809 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1868119619) ^ 464822 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1868119619) ^ 8038 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1931195141 : Nat.Prime 1931195141 := by
  apply lucas_primality 1931195141 (2 : ZMod 1931195141)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1447, 1), (9533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1447, 1), (9533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1931195141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_1447
      · exact prime_fiftyAV_9533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1931195141) ^ 965597570 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931195141) ^ 386239028 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931195141) ^ 275885020 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931195141) ^ 1334620 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931195141) ^ 202580 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1951572421 : Nat.Prime 1951572421 := by
  apply lucas_primality 1951572421 (10 : ZMod 1951572421)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (89, 1), (5801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951572421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_89
      · exact prime_fiftyAV_5801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1951572421) ^ 975786210 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 650524140 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 390314484 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 278796060 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 21927780 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1951572421) ^ 336420 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1951638919 : Nat.Prime 1951638919 := by
  apply lucas_primality 1951638919 (3 : ZMod 1951638919)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (14142311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (14142311, 1)] : List FactorBlock).map factorBlockValue).prod) = 1951638919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_14142311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1951638919) ^ 975819459 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1951638919) ^ 650546306 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1951638919) ^ 84853866 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1951638919) ^ 138 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2013321539 : Nat.Prime 2013321539 := by
  apply lucas_primality 2013321539 (2 : ZMod 2013321539)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (12128443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (12128443, 1)] : List FactorBlock).map factorBlockValue).prod) = 2013321539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_83
      · exact prime_fiftyAV_12128443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2013321539) ^ 1006660769 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013321539) ^ 24256886 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2013321539) ^ 166 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2049369011 : Nat.Prime 2049369011 := by
  apply lucas_primality 2049369011 (2 : ZMod 2049369011)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (41, 1), (384497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (41, 1), (384497, 1)] : List FactorBlock).map factorBlockValue).prod) = 2049369011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_384497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2049369011) ^ 1024684505 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2049369011) ^ 409873802 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2049369011) ^ 157643770 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2049369011) ^ 49984610 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2049369011) ^ 5330 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2061564319 : Nat.Prime 2061564319 := by
  apply lucas_primality 2061564319 (6 : ZMod 2061564319)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (3470647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (3470647, 1)] : List FactorBlock).map factorBlockValue).prod) = 2061564319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_3470647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2061564319) ^ 1030782159 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2061564319) ^ 687188106 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2061564319) ^ 187414938 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 2061564319) ^ 594 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2072555033 : Nat.Prime 2072555033 := by
  apply lucas_primality 2072555033 (3 : ZMod 2072555033)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (4247039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (4247039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2072555033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_61
      · exact prime_fiftyAV_4247039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2072555033) ^ 1036277516 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2072555033) ^ 33976312 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2072555033) ^ 488 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2151605849 : Nat.Prime 2151605849 := by
  apply lucas_primality 2151605849 (3 : ZMod 2151605849)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (38421533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (38421533, 1)] : List FactorBlock).map factorBlockValue).prod) = 2151605849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_38421533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2151605849) ^ 1075802924 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2151605849) ^ 307372264 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2151605849) ^ 56 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2394574277 : Nat.Prime 2394574277 := by
  apply lucas_primality 2394574277 (2 : ZMod 2394574277)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (9813829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394574277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_61
      · exact prime_fiftyAV_9813829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2394574277) ^ 1197287138 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 39255316 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2394574277) ^ 244 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_3025257869 : Nat.Prime 3025257869 := by
  apply lucas_primality 3025257869 (2 : ZMod 3025257869)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (756314467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (756314467, 1)] : List FactorBlock).map factorBlockValue).prod) = 3025257869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_756314467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3025257869) ^ 1512628934 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3025257869) ^ 4 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_3862390283 : Nat.Prime 3862390283 := by
  apply lucas_primality 3862390283 (2 : ZMod 3862390283)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1931195141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1931195141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3862390283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_1931195141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3862390283) ^ 1931195141 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3862390283) ^ 2 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_5696273509 : Nat.Prime 5696273509 := by
  apply lucas_primality 5696273509 (2 : ZMod 5696273509)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3571, 1), (132929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3571, 1), (132929, 1)] : List FactorBlock).map factorBlockValue).prod) = 5696273509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_3571
      · exact prime_fiftyAV_132929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5696273509) ^ 2848136754 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5696273509) ^ 1898757836 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5696273509) ^ 1595148 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5696273509) ^ 42852 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_6057583319 : Nat.Prime 6057583319 := by
  apply lucas_primality 6057583319 (7 : ZMod 6057583319)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (557, 1), (32561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (557, 1), (32561, 1)] : List FactorBlock).map factorBlockValue).prod) = 6057583319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_167
      · exact prime_fiftyAV_557
      · exact prime_fiftyAV_32561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6057583319) ^ 3028791659 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 6057583319) ^ 36272954 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 6057583319) ^ 10875374 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 6057583319) ^ 186038 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_6786591521 : Nat.Prime 6786591521 := by
  apply lucas_primality 6786591521 (3 : ZMod 6786591521)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (42416197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (42416197, 1)] : List FactorBlock).map factorBlockValue).prod) = 6786591521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_42416197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6786591521) ^ 3393295760 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6786591521) ^ 1357318304 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6786591521) ^ 160 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_7183291789 : Nat.Prime 7183291789 := by
  apply lucas_primality 7183291789 (6 : ZMod 7183291789)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (149, 1), (446389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (149, 1), (446389, 1)] : List FactorBlock).map factorBlockValue).prod) = 7183291789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_149
      · exact prime_fiftyAV_446389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 7183291789) ^ 3591645894 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7183291789) ^ 2394430596 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7183291789) ^ 48210012 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 7183291789) ^ 16092 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_7311057107 : Nat.Prime 7311057107 := by
  apply lucas_primality 7311057107 (2 : ZMod 7311057107)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (2409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 7311057107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_2409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7311057107) ^ 3655528553 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 197596138 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 178318466 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7311057107) ^ 3034 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_10834859807 : Nat.Prime 10834859807 := by
  apply lucas_primality 10834859807 (5 : ZMod 10834859807)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30097, 1), (179999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30097, 1), (179999, 1)] : List FactorBlock).map factorBlockValue).prod) = 10834859807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_30097
      · exact prime_fiftyAV_179999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10834859807) ^ 5417429903 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 10834859807) ^ 359998 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 10834859807) ^ 60194 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_13769726743 : Nat.Prime 13769726743 := by
  apply lucas_primality 13769726743 (3 : ZMod 13769726743)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (5563, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (5563, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) = 13769726743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_5563
      · exact prime_fiftyAV_8089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13769726743) ^ 6884863371 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13769726743) ^ 4589908914 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13769726743) ^ 809983926 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13769726743) ^ 2475234 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13769726743) ^ 1702278 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_13852339783 : Nat.Prime 13852339783 := by
  apply lucas_primality 13852339783 (3 : ZMod 13852339783)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (619, 1), (10687, 1)] : List FactorBlock).map factorBlockValue).prod) = 13852339783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_349
      · exact prime_fiftyAV_619
      · exact prime_fiftyAV_10687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13852339783) ^ 6926169891 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 4617446594 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 39691518 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 22378578 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 13852339783) ^ 1296186 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_14367445663 : Nat.Prime 14367445663 := by
  apply lucas_primality 14367445663 (23 : ZMod 14367445663)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394574277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14367445663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_2394574277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 14367445663) ^ 7183722831 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 4789148554 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (23 : ZMod 14367445663) ^ 6 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_14594220139 : Nat.Prime 14594220139 := by
  apply lucas_primality 14594220139 (7 : ZMod 14594220139)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6131, 1), (396733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6131, 1), (396733, 1)] : List FactorBlock).map factorBlockValue).prod) = 14594220139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_6131
      · exact prime_fiftyAV_396733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14594220139) ^ 7297110069 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 14594220139) ^ 4864740046 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 14594220139) ^ 2380398 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 14594220139) ^ 36786 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_15535459337 : Nat.Prime 15535459337 := by
  apply lucas_primality 15535459337 (3 : ZMod 15535459337)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (47, 1), (79, 1), (12163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (47, 1), (79, 1), (12163, 1)] : List FactorBlock).map factorBlockValue).prod) = 15535459337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_12163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15535459337) ^ 7767729668 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15535459337) ^ 361289752 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15535459337) ^ 330541688 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15535459337) ^ 196651384 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15535459337) ^ 1277272 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_16160002907 : Nat.Prime 16160002907 := by
  apply lucas_primality 16160002907 (2 : ZMod 16160002907)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (351304411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (351304411, 1)] : List FactorBlock).map factorBlockValue).prod) = 16160002907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_351304411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16160002907) ^ 8080001453 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16160002907) ^ 702608822 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16160002907) ^ 46 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_17755350889 : Nat.Prime 17755350889 := by
  apply lucas_primality 17755350889 (14 : ZMod 17755350889)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (3539743, 1)] : List FactorBlock).map factorBlockValue).prod) = 17755350889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_3539743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 17755350889) ^ 8877675444 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5918450296 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 1614122808 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 934492152 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 17755350889) ^ 5016 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_19804931479 : Nat.Prime 19804931479 := by
  apply lucas_primality 19804931479 (3 : ZMod 19804931479)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1100273971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1100273971, 1)] : List FactorBlock).map factorBlockValue).prod) = 19804931479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_1100273971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19804931479) ^ 9902465739 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19804931479) ^ 6601643826 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19804931479) ^ 18 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_20735701603 : Nat.Prime 20735701603 := by
  apply lucas_primality 20735701603 (2 : ZMod 20735701603)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (599, 1), (74929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (599, 1), (74929, 1)] : List FactorBlock).map factorBlockValue).prod) = 20735701603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_599
      · exact prime_fiftyAV_74929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20735701603) ^ 10367850801 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20735701603) ^ 6911900534 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20735701603) ^ 2962243086 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20735701603) ^ 1885063782 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20735701603) ^ 34617198 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20735701603) ^ 276738 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_21779857369 : Nat.Prime 21779857369 := by
  apply lucas_primality 21779857369 (22 : ZMod 21779857369)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (33610891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (33610891, 1)] : List FactorBlock).map factorBlockValue).prod) = 21779857369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_33610891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (22 : ZMod 21779857369) ^ 10889928684 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (22 : ZMod 21779857369) ^ 7259952456 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (22 : ZMod 21779857369) ^ 648 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_21796943101 : Nat.Prime 21796943101 := by
  apply lucas_primality 21796943101 (10 : ZMod 21796943101)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (181, 1), (401417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (181, 1), (401417, 1)] : List FactorBlock).map factorBlockValue).prod) = 21796943101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_181
      · exact prime_fiftyAV_401417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21796943101) ^ 10898471550 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 21796943101) ^ 7265647700 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 21796943101) ^ 4359388620 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 21796943101) ^ 120425100 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 21796943101) ^ 54300 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_24330664621 : Nat.Prime 24330664621 := by
  apply lucas_primality 24330664621 (2 : ZMod 24330664621)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (135170359, 1)] : List FactorBlock).map factorBlockValue).prod) = 24330664621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_135170359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24330664621) ^ 12165332310 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 8110221540 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 4866132924 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24330664621) ^ 180 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_28564904807 : Nat.Prime 28564904807 := by
  apply lucas_primality 28564904807 (5 : ZMod 28564904807)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (840144259, 1)] : List FactorBlock).map factorBlockValue).prod) = 28564904807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_840144259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28564904807) ^ 14282452403 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 1680288518 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 28564904807) ^ 34 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_30890258779 : Nat.Prime 30890258779 := by
  apply lucas_primality 30890258779 (3 : ZMod 30890258779)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2111, 1), (2438833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2111, 1), (2438833, 1)] : List FactorBlock).map factorBlockValue).prod) = 30890258779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_2111
      · exact prime_fiftyAV_2438833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30890258779) ^ 15445129389 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30890258779) ^ 10296752926 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30890258779) ^ 14632998 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30890258779) ^ 12666 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_151
      · exact prime_fiftyAV_479
      · exact prime_fiftyAV_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_54743994013 : Nat.Prime 54743994013 := by
  apply lucas_primality 54743994013 (2 : ZMod 54743994013)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (113, 1), (163, 1), (233, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (113, 1), (163, 1), (233, 1), (1063, 1)] : List FactorBlock).map factorBlockValue).prod) = 54743994013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_113
      · exact prime_fiftyAV_163
      · exact prime_fiftyAV_233
      · exact prime_fiftyAV_1063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54743994013) ^ 27371997006 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 18247998004 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 484460124 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 335852724 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 234952764 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54743994013) ^ 51499524 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_56463796133 : Nat.Prime 56463796133 := by
  apply lucas_primality 56463796133 (2 : ZMod 56463796133)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (266338661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (266338661, 1)] : List FactorBlock).map factorBlockValue).prod) = 56463796133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_266338661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56463796133) ^ 28231898066 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 56463796133) ^ 1065354644 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 56463796133) ^ 212 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_58376880557 : Nat.Prime 58376880557 := by
  apply lucas_primality 58376880557 (2 : ZMod 58376880557)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14594220139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14594220139, 1)] : List FactorBlock).map factorBlockValue).prod) = 58376880557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_14594220139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 58376880557) ^ 29188440278 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58376880557) ^ 4 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_58488456857 : Nat.Prime 58488456857 := by
  apply lucas_primality 58488456857 (3 : ZMod 58488456857)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7311057107, 1)] : List FactorBlock).map factorBlockValue).prod) = 58488456857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7311057107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 58488456857) ^ 29244228428 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 58488456857) ^ 8 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_58596351661 : Nat.Prime 58596351661 := by
  apply lucas_primality 58596351661 (2 : ZMod 58596351661)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (11, 1), (37, 1), (163, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (11, 1), (37, 1), (163, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) = 58596351661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_163
      · exact prime_fiftyAV_701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58596351661) ^ 29298175830 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 19532117220 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 11719270332 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 8370907380 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 5326941060 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 1583685180 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 359486820 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58596351661) ^ 83589660 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_66920585423 : Nat.Prime 66920585423 := by
  apply lucas_primality 66920585423 (5 : ZMod 66920585423)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (79, 1), (3301, 1), (4139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (79, 1), (3301, 1), (4139, 1)] : List FactorBlock).map factorBlockValue).prod) = 66920585423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_3301
      · exact prime_fiftyAV_4139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 66920585423) ^ 33460292711 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 66920585423) ^ 2158728562 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 66920585423) ^ 847096018 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 66920585423) ^ 20272822 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 66920585423) ^ 16168298 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_81709378843 : Nat.Prime 81709378843 := by
  apply lucas_primality 81709378843 (5 : ZMod 81709378843)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (149650877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (149650877, 1)] : List FactorBlock).map factorBlockValue).prod) = 81709378843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_149650877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 81709378843) ^ 40854689421 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 81709378843) ^ 27236459614 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 81709378843) ^ 11672768406 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 81709378843) ^ 6285336834 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 81709378843) ^ 546 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_87119429477 : Nat.Prime 87119429477 := by
  apply lucas_primality 87119429477 (2 : ZMod 87119429477)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (21779857369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (21779857369, 1)] : List FactorBlock).map factorBlockValue).prod) = 87119429477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_21779857369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 87119429477) ^ 43559714738 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 87119429477) ^ 4 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_102452651107 : Nat.Prime 102452651107 := by
  apply lucas_primality 102452651107 (2 : ZMod 102452651107)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (71, 1), (97, 1), (269, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (71, 1), (97, 1), (269, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod) = 102452651107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_71
      · exact prime_fiftyAV_97
      · exact prime_fiftyAV_269
      · exact prime_fiftyAV_709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102452651107) ^ 51226325553 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452651107) ^ 34150883702 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452651107) ^ 7880973162 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452651107) ^ 1442995086 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452651107) ^ 1056212898 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452651107) ^ 380864874 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 102452651107) ^ 144503034 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_114759356801 : Nat.Prime 114759356801 := by
  apply lucas_primality 114759356801 (3 : ZMod 114759356801)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (11, 1), (17, 2), (29, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (11, 1), (17, 2), (29, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 114759356801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 114759356801) ^ 57379678400 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 114759356801) ^ 22951871360 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 114759356801) ^ 10432668800 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 114759356801) ^ 6750550400 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 114759356801) ^ 3957219200 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 114759356801) ^ 295011200 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_120249334741 : Nat.Prime 120249334741 := by
  apply lucas_primality 120249334741 (14 : ZMod 120249334741)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (37, 1), (163, 1), (332309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (37, 1), (163, 1), (332309, 1)] : List FactorBlock).map factorBlockValue).prod) = 120249334741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_163
      · exact prime_fiftyAV_332309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 120249334741) ^ 60124667370 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 120249334741) ^ 40083111580 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 120249334741) ^ 24049866948 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 120249334741) ^ 3249982020 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 120249334741) ^ 737725980 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 120249334741) ^ 361860 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_122671363769 : Nat.Prime 122671363769 := by
  apply lucas_primality 122671363769 (3 : ZMod 122671363769)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (414430283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (414430283, 1)] : List FactorBlock).map factorBlockValue).prod) = 122671363769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_414430283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 122671363769) ^ 61335681884 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 122671363769) ^ 3315442264 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 122671363769) ^ 296 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_158251239389 : Nat.Prime 158251239389 := by
  apply lucas_primality 158251239389 (2 : ZMod 158251239389)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (37, 1), (983, 1), (98887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (37, 1), (983, 1), (98887, 1)] : List FactorBlock).map factorBlockValue).prod) = 158251239389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_983
      · exact prime_fiftyAV_98887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158251239389) ^ 79125619694 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158251239389) ^ 14386476308 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158251239389) ^ 4277060524 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158251239389) ^ 160988036 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158251239389) ^ 1600324 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_177829524883 : Nat.Prime 177829524883 := by
  apply lucas_primality 177829524883 (2 : ZMod 177829524883)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 2), (5039, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 2), (5039, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) = 177829524883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_5039
      · exact prime_fiftyAV_5431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 177829524883) ^ 88914762441 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 177829524883) ^ 59276508294 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 177829524883) ^ 9359448678 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 177829524883) ^ 35290638 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 177829524883) ^ 32743422 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_219613389623 : Nat.Prime 219613389623 := by
  apply lucas_primality 219613389623 (5 : ZMod 219613389623)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (163646341, 1)] : List FactorBlock).map factorBlockValue).prod) = 219613389623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_61
      · exact prime_fiftyAV_163646341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 219613389623) ^ 109806694811 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 19964853602 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 3600219502 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 219613389623) ^ 1342 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_237841108607 : Nat.Prime 237841108607 := by
  apply lucas_primality 237841108607 (5 : ZMod 237841108607)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1093, 1), (3509741, 1)] : List FactorBlock).map factorBlockValue).prod) = 237841108607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_1093
      · exact prime_fiftyAV_3509741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 237841108607) ^ 118920554303 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 7672293826 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 217603942 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 237841108607) ^ 67766 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_243797203261 : Nat.Prime 243797203261 := by
  apply lucas_primality 243797203261 (6 : ZMod 243797203261)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (9421, 1), (11059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (9421, 1), (11059, 1)] : List FactorBlock).map factorBlockValue).prod) = 243797203261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_9421
      · exact prime_fiftyAV_11059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 243797203261) ^ 121898601630 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 243797203261) ^ 81265734420 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 243797203261) ^ 48759440652 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 243797203261) ^ 18753631020 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 243797203261) ^ 25878060 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 243797203261) ^ 22045140 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_253396446841 : Nat.Prime 253396446841 := by
  apply lucas_primality 253396446841 (7 : ZMod 253396446841)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (67, 1), (71, 1), (79, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (67, 1), (71, 1), (79, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) = 253396446841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_67
      · exact prime_fiftyAV_71
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_1873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 253396446841) ^ 126698223420 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 253396446841) ^ 84465482280 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 253396446841) ^ 50679289368 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 253396446841) ^ 3782036520 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 253396446841) ^ 3568964040 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 253396446841) ^ 3207549960 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 253396446841) ^ 135289080 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_255707684119 : Nat.Prime 255707684119 := by
  apply lucas_primality 255707684119 (3 : ZMod 255707684119)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (26423, 1), (537637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (26423, 1), (537637, 1)] : List FactorBlock).map factorBlockValue).prod) = 255707684119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_26423
      · exact prime_fiftyAV_537637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 255707684119) ^ 127853842059 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 255707684119) ^ 85235894706 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 255707684119) ^ 9677466 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 255707684119) ^ 475614 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_316502478779 : Nat.Prime 316502478779 := by
  apply lucas_primality 316502478779 (2 : ZMod 316502478779)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (158251239389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (158251239389, 1)] : List FactorBlock).map factorBlockValue).prod) = 316502478779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_158251239389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 316502478779) ^ 158251239389 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 316502478779) ^ 2 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_338782776799 : Nat.Prime 338782776799 := by
  apply lucas_primality 338782776799 (3 : ZMod 338782776799)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (56463796133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (56463796133, 1)] : List FactorBlock).map factorBlockValue).prod) = 338782776799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_56463796133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 338782776799) ^ 169391388399 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 338782776799) ^ 112927592266 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 338782776799) ^ 6 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_428348173229 : Nat.Prime 428348173229 := by
  apply lucas_primality 428348173229 (2 : ZMod 428348173229)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4999, 1), (21421693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4999, 1), (21421693, 1)] : List FactorBlock).map factorBlockValue).prod) = 428348173229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_4999
      · exact prime_fiftyAV_21421693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 428348173229) ^ 214174086614 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 428348173229) ^ 85686772 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 428348173229) ^ 19996 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_397
      · exact prime_fiftyAV_2531
      · exact prime_fiftyAV_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_642024344141 : Nat.Prime 642024344141 := by
  apply lucas_primality 642024344141 (2 : ZMod 642024344141)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (601, 1), (1669, 1), (32003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (601, 1), (1669, 1), (32003, 1)] : List FactorBlock).map factorBlockValue).prod) = 642024344141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_601
      · exact prime_fiftyAV_1669
      · exact prime_fiftyAV_32003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642024344141) ^ 321012172070 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 642024344141) ^ 128404868828 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 642024344141) ^ 1068260140 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 642024344141) ^ 384676060 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 642024344141) ^ 20061380 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_650051402041 : Nat.Prime 650051402041 := by
  apply lucas_primality 650051402041 (11 : ZMod 650051402041)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (79, 1), (199, 1), (114859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (79, 1), (199, 1), (114859, 1)] : List FactorBlock).map factorBlockValue).prod) = 650051402041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_199
      · exact prime_fiftyAV_114859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 650051402041) ^ 325025701020 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 216683800680 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 130010280408 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 8228498760 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 3266589960 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 650051402041) ^ 5659560 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_702509983793 : Nat.Prime 702509983793 := by
  apply lucas_primality 702509983793 (3 : ZMod 702509983793)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (131, 1), (16567, 1), (20231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (131, 1), (16567, 1), (20231, 1)] : List FactorBlock).map factorBlockValue).prod) = 702509983793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_131
      · exact prime_fiftyAV_16567
      · exact prime_fiftyAV_20231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 702509983793) ^ 351254991896 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 702509983793) ^ 5362671632 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 702509983793) ^ 42404176 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 702509983793) ^ 34724432 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1065742907407 : Nat.Prime 1065742907407 := by
  apply lucas_primality 1065742907407 (5 : ZMod 1065742907407)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36997, 1), (4801033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36997, 1), (4801033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065742907407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_36997
      · exact prime_fiftyAV_4801033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1065742907407) ^ 532871453703 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065742907407) ^ 355247635802 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065742907407) ^ 28806198 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065742907407) ^ 221982 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1066883369399 : Nat.Prime 1066883369399 := by
  apply lucas_primality 1066883369399 (11 : ZMod 1066883369399)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (131, 1), (3967, 1), (13331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (131, 1), (3967, 1), (13331, 1)] : List FactorBlock).map factorBlockValue).prod) = 1066883369399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_131
      · exact prime_fiftyAV_3967
      · exact prime_fiftyAV_13331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1066883369399) ^ 533441684699 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 152411909914 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 96989397218 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 8144147858 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 268939594 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1066883369399) ^ 80030258 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1130831493331 : Nat.Prime 1130831493331 := by
  apply lucas_primality 1130831493331 (2 : ZMod 1130831493331)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (67, 1), (569, 1), (12841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (67, 1), (569, 1), (12841, 1)] : List FactorBlock).map factorBlockValue).prod) = 1130831493331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_67
      · exact prime_fiftyAV_569
      · exact prime_fiftyAV_12841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1130831493331) ^ 565415746665 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 376943831110 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 226166298666 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 161547356190 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 102802863030 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 16878081990 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 1987401570 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130831493331) ^ 88064130 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1185399396581 : Nat.Prime 1185399396581 := by
  apply lucas_primality 1185399396581 (2 : ZMod 1185399396581)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (137, 1), (389, 1), (22697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (137, 1), (389, 1), (22697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1185399396581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_137
      · exact prime_fiftyAV_389
      · exact prime_fiftyAV_22697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1185399396581) ^ 592699698290 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 237079879316 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 169342770940 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 8652550340 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 3047299220 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185399396581) ^ 52227140 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1338411708461 : Nat.Prime 1338411708461 := by
  apply lucas_primality 1338411708461 (2 : ZMod 1338411708461)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (66920585423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (66920585423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1338411708461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_66920585423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1338411708461) ^ 669205854230 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338411708461) ^ 267682341692 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338411708461) ^ 20 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1368556305799 : Nat.Prime 1368556305799 := by
  apply lucas_primality 1368556305799 (3 : ZMod 1368556305799)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (20735701603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (20735701603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1368556305799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_20735701603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1368556305799) ^ 684278152899 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1368556305799) ^ 456185435266 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1368556305799) ^ 124414209618 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1368556305799) ^ 66 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1405019967587 : Nat.Prime 1405019967587 := by
  apply lucas_primality 1405019967587 (2 : ZMod 1405019967587)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (702509983793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (702509983793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1405019967587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_702509983793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1405019967587) ^ 702509983793 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1405019967587) ^ 2 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1406212853597 : Nat.Prime 1406212853597 := by
  apply lucas_primality 1406212853597 (2 : ZMod 1406212853597)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (977, 1), (906371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1406212853597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_397
      · exact prime_fiftyAV_977
      · exact prime_fiftyAV_906371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1406212853597) ^ 703106426798 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 3542097868 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1439317148 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1406212853597) ^ 1551476 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1447535876737 : Nat.Prime 1447535876737 := by
  apply lucas_primality 1447535876737 (7 : ZMod 1447535876737)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (9137, 1), (412567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (9137, 1), (412567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1447535876737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_9137
      · exact prime_fiftyAV_412567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1447535876737) ^ 723767938368 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1447535876737) ^ 482511958912 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1447535876737) ^ 158425728 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1447535876737) ^ 3508608 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1483112670203 : Nat.Prime 1483112670203 := by
  apply lucas_primality 1483112670203 (2 : ZMod 1483112670203)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (30871, 1), (1044397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1483112670203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_30871
      · exact prime_fiftyAV_1044397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1483112670203) ^ 741556335101 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 64483159574 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 48042262 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483112670203) ^ 1420066 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_35279
      · exact prime_fiftyAV_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1529752406099 : Nat.Prime 1529752406099 := by
  apply lucas_primality 1529752406099 (2 : ZMod 1529752406099)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (89, 1), (617, 1), (42337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1529752406099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_89
      · exact prime_fiftyAV_617
      · exact prime_fiftyAV_42337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1529752406099) ^ 764876203049 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 218536058014 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 32547923534 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 17188229282 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 2479339394 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1529752406099) ^ 36132754 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1726920139561 : Nat.Prime 1726920139561 := by
  apply lucas_primality 1726920139561 (23 : ZMod 1726920139561)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (12809, 1), (14591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (12809, 1), (14591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1726920139561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_12809
      · exact prime_fiftyAV_14591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1726920139561) ^ 863460069780 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 575640046520 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 345384027912 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 246702877080 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 156992739960 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 134820840 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (23 : ZMod 1726920139561) ^ 118355160 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1742833970153 : Nat.Prime 1742833970153 := by
  apply lucas_primality 1742833970153 (3 : ZMod 1742833970153)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19804931479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19804931479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1742833970153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_19804931479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1742833970153) ^ 871416985076 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1742833970153) ^ 158439451832 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1742833970153) ^ 88 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2091461964649 : Nat.Prime 2091461964649 := by
  apply lucas_primality 2091461964649 (13 : ZMod 2091461964649)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (78041, 1), (159521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (78041, 1), (159521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2091461964649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_78041
      · exact prime_fiftyAV_159521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2091461964649) ^ 1045730982324 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2091461964649) ^ 697153988216 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2091461964649) ^ 298780280664 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2091461964649) ^ 26799528 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2091461964649) ^ 13110888 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2625207939961 : Nat.Prime 2625207939961 := by
  apply lucas_primality 2625207939961 (14 : ZMod 2625207939961)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (239, 1), (1303, 1), (70249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (239, 1), (1303, 1), (70249, 1)] : List FactorBlock).map factorBlockValue).prod) = 2625207939961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_239
      · exact prime_fiftyAV_1303
      · exact prime_fiftyAV_70249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2625207939961) ^ 1312603969980 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 875069313320 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 525041587992 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 10984133640 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 2014741320 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 2625207939961) ^ 37370040 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2659378548317 : Nat.Prime 2659378548317 := by
  apply lucas_primality 2659378548317 (2 : ZMod 2659378548317)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (10667, 1), (8903891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (10667, 1), (8903891, 1)] : List FactorBlock).map factorBlockValue).prod) = 2659378548317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_10667
      · exact prime_fiftyAV_8903891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2659378548317) ^ 1329689274158 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2659378548317) ^ 379911221188 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2659378548317) ^ 249308948 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2659378548317) ^ 298676 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2970293224763 : Nat.Prime 2970293224763 := by
  apply lucas_primality 2970293224763 (2 : ZMod 2970293224763)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (761, 1), (1951572421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970293224763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_761
      · exact prime_fiftyAV_1951572421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2970293224763) ^ 1485146612381 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 3903144842 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970293224763) ^ 1522 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_3031576734283 : Nat.Prime 3031576734283 := by
  apply lucas_primality 3031576734283 (13 : ZMod 3031576734283)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (293, 1), (1724446379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (293, 1), (1724446379, 1)] : List FactorBlock).map factorBlockValue).prod) = 3031576734283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_293
      · exact prime_fiftyAV_1724446379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3031576734283) ^ 1515788367141 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 3031576734283) ^ 1010525578094 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 3031576734283) ^ 10346678274 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 3031576734283) ^ 1758 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_3628626968867 : Nat.Prime 3628626968867 := by
  apply lucas_primality 3628626968867 (2 : ZMod 3628626968867)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4357, 1), (416413469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4357, 1), (416413469, 1)] : List FactorBlock).map factorBlockValue).prod) = 3628626968867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_4357
      · exact prime_fiftyAV_416413469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3628626968867) ^ 1814313484433 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3628626968867) ^ 832826938 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3628626968867) ^ 8714 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_3828156095761 : Nat.Prime 3828156095761 := by
  apply lucas_primality 3828156095761 (11 : ZMod 3828156095761)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (89, 1), (4229, 1), (42379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (89, 1), (4229, 1), (42379, 1)] : List FactorBlock).map factorBlockValue).prod) = 3828156095761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_89
      · exact prime_fiftyAV_4229
      · exact prime_fiftyAV_42379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3828156095761) ^ 1914078047880 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3828156095761) ^ 1276052031920 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3828156095761) ^ 765631219152 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3828156095761) ^ 43012989840 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3828156095761) ^ 905215440 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3828156095761) ^ 90331440 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_5099327703787 : Nat.Prime 5099327703787 := by
  apply lucas_primality 5099327703787 (3 : ZMod 5099327703787)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (381559, 1), (2227409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5099327703787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_381559
      · exact prime_fiftyAV_2227409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5099327703787) ^ 2549663851893 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 1699775901262 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 13364454 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5099327703787) ^ 2289354 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_5597206986757 : Nat.Prime 5597206986757 := by
  apply lucas_primality 5597206986757 (2 : ZMod 5597206986757)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (6057583319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (6057583319, 1)] : List FactorBlock).map factorBlockValue).prod) = 5597206986757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_6057583319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5597206986757) ^ 2798603493378 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5597206986757) ^ 1865735662252 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5597206986757) ^ 799600998108 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5597206986757) ^ 508836998796 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5597206986757) ^ 924 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_5917576318961 : Nat.Prime 5917576318961 := by
  apply lucas_primality 5917576318961 (3 : ZMod 5917576318961)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (419, 1), (4111, 1), (42943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (419, 1), (4111, 1), (42943, 1)] : List FactorBlock).map factorBlockValue).prod) = 5917576318961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_419
      · exact prime_fiftyAV_4111
      · exact prime_fiftyAV_42943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5917576318961) ^ 2958788159480 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917576318961) ^ 1183515263792 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917576318961) ^ 14123093840 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917576318961) ^ 1439449360 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917576318961) ^ 137800720 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_6279845155949 : Nat.Prime 6279845155949 := by
  apply lucas_primality 6279845155949 (2 : ZMod 6279845155949)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (89, 1), (2053, 1), (94421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (89, 1), (2053, 1), (94421, 1)] : List FactorBlock).map factorBlockValue).prod) = 6279845155949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_89
      · exact prime_fiftyAV_2053
      · exact prime_fiftyAV_94421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6279845155949) ^ 3139922577974 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 897120736564 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 483065011996 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 70560057932 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 3058862716 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6279845155949) ^ 66508988 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_8683013175229 : Nat.Prime 8683013175229 := by
  apply lucas_primality 8683013175229 (2 : ZMod 8683013175229)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (347, 1), (33099329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (347, 1), (33099329, 1)] : List FactorBlock).map factorBlockValue).prod) = 8683013175229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_347
      · exact prime_fiftyAV_33099329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8683013175229) ^ 4341506587614 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8683013175229) ^ 2894337725076 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8683013175229) ^ 1240430453604 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8683013175229) ^ 25023092724 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8683013175229) ^ 262332 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_9825009110321 : Nat.Prime 9825009110321 := by
  apply lucas_primality 9825009110321 (3 : ZMod 9825009110321)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (61, 1), (2013321539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (61, 1), (2013321539, 1)] : List FactorBlock).map factorBlockValue).prod) = 9825009110321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_61
      · exact prime_fiftyAV_2013321539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9825009110321) ^ 4912504555160 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9825009110321) ^ 1965001822064 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9825009110321) ^ 161065723120 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9825009110321) ^ 4880 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_10724678746921 : Nat.Prime 10724678746921 := by
  apply lucas_primality 10724678746921 (11 : ZMod 10724678746921)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 7), (5, 1), (947, 1), (129457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 7), (5, 1), (947, 1), (129457, 1)] : List FactorBlock).map factorBlockValue).prod) = 10724678746921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_947
      · exact prime_fiftyAV_129457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10724678746921) ^ 5362339373460 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10724678746921) ^ 3574892915640 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10724678746921) ^ 2144935749384 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10724678746921) ^ 11324898360 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10724678746921) ^ 82843560 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_11074551087949 : Nat.Prime 11074551087949 := by
  apply lucas_primality 11074551087949 (2 : ZMod 11074551087949)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (19, 1), (71, 1), (1151, 1), (34963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (19, 1), (71, 1), (1151, 1), (34963, 1)] : List FactorBlock).map factorBlockValue).prod) = 11074551087949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_71
      · exact prime_fiftyAV_1151
      · exact prime_fiftyAV_34963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11074551087949) ^ 5537275543974 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 3691517029316 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 651444181644 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 582871109892 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 155979592788 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 9621677748 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11074551087949) ^ 316750596 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_19649401054343 : Nat.Prime 19649401054343 := by
  apply lucas_primality 19649401054343 (5 : ZMod 19649401054343)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (338782776799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (338782776799, 1)] : List FactorBlock).map factorBlockValue).prod) = 19649401054343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_338782776799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 19649401054343) ^ 9824700527171 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 19649401054343) ^ 677565553598 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 19649401054343) ^ 58 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_20171893710853 : Nat.Prime 20171893710853 := by
  apply lucas_primality 20171893710853 (5 : ZMod 20171893710853)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (14367445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171893710853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_14367445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20171893710853) ^ 10085946855426 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 6723964570284 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1551684131604 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 20171893710853) ^ 1404 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_26932669760303 : Nat.Prime 26932669760303 := by
  apply lucas_primality 26932669760303 (5 : ZMod 26932669760303)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16417, 1), (820267703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16417, 1), (820267703, 1)] : List FactorBlock).map factorBlockValue).prod) = 26932669760303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_16417
      · exact prime_fiftyAV_820267703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26932669760303) ^ 13466334880151 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 26932669760303) ^ 1640535406 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 26932669760303) ^ 32834 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_28160906695139 : Nat.Prime 28160906695139 := by
  apply lucas_primality 28160906695139 (2 : ZMod 28160906695139)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (131, 1), (2621, 1), (5858417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (131, 1), (2621, 1), (5858417, 1)] : List FactorBlock).map factorBlockValue).prod) = 28160906695139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_131
      · exact prime_fiftyAV_2621
      · exact prime_fiftyAV_5858417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28160906695139) ^ 14080453347569 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28160906695139) ^ 4022986670734 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28160906695139) ^ 214968753398 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28160906695139) ^ 10744336778 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28160906695139) ^ 4806914 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_31084562512099 : Nat.Prime 31084562512099 := by
  apply lucas_primality 31084562512099 (2 : ZMod 31084562512099)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1726920139561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1726920139561, 1)] : List FactorBlock).map factorBlockValue).prod) = 31084562512099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_1726920139561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31084562512099) ^ 15542281256049 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31084562512099) ^ 10361520837366 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 31084562512099) ^ 18 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_33265025793757 : Nat.Prime 33265025793757 := by
  apply lucas_primality 33265025793757 (2 : ZMod 33265025793757)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (121591, 1), (7599481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (121591, 1), (7599481, 1)] : List FactorBlock).map factorBlockValue).prod) = 33265025793757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_121591
      · exact prime_fiftyAV_7599481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33265025793757) ^ 16632512896878 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33265025793757) ^ 11088341931252 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33265025793757) ^ 273581316 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33265025793757) ^ 4377276 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_50248681511863 : Nat.Prime 50248681511863 := by
  apply lucas_primality 50248681511863 (3 : ZMod 50248681511863)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4483, 1), (1868119619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4483, 1), (1868119619, 1)] : List FactorBlock).map factorBlockValue).prod) = 50248681511863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_4483
      · exact prime_fiftyAV_1868119619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50248681511863) ^ 25124340755931 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 50248681511863) ^ 16749560503954 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 50248681511863) ^ 11208717714 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 50248681511863) ^ 26898 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_67892046667391 : Nat.Prime 67892046667391 := by
  apply lucas_primality 67892046667391 (7 : ZMod 67892046667391)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (479, 1), (643, 1), (2003917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (479, 1), (643, 1), (2003917, 1)] : List FactorBlock).map factorBlockValue).prod) = 67892046667391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_479
      · exact prime_fiftyAV_643
      · exact prime_fiftyAV_2003917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 67892046667391) ^ 33946023333695 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 67892046667391) ^ 13578409333478 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 67892046667391) ^ 6172004242490 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 67892046667391) ^ 141737049410 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 67892046667391) ^ 105586386730 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 67892046667391) ^ 33879670 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_70951236721691 : Nat.Prime 70951236721691 := by
  apply lucas_primality 70951236721691 (2 : ZMod 70951236721691)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (409, 1), (1334422357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (409, 1), (1334422357, 1)] : List FactorBlock).map factorBlockValue).prod) = 70951236721691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_409
      · exact prime_fiftyAV_1334422357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70951236721691) ^ 35475618360845 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 70951236721691) ^ 14190247344338 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 70951236721691) ^ 5457787440130 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 70951236721691) ^ 173474906410 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 70951236721691) ^ 53170 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_74447328298097 : Nat.Prime 74447328298097 := by
  apply lucas_primality 74447328298097 (3 : ZMod 74447328298097)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (131, 1), (2287, 1), (1194671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (131, 1), (2287, 1), (1194671, 1)] : List FactorBlock).map factorBlockValue).prod) = 74447328298097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_131
      · exact prime_fiftyAV_2287
      · exact prime_fiftyAV_1194671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 74447328298097) ^ 37223664149048 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 74447328298097) ^ 5726717561392 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 74447328298097) ^ 568300216016 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 74447328298097) ^ 32552395408 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 74447328298097) ^ 62316176 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_87490457571481 : Nat.Prime 87490457571481 := by
  apply lucas_primality 87490457571481 (7 : ZMod 87490457571481)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (241, 1), (3025257869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (241, 1), (3025257869, 1)] : List FactorBlock).map factorBlockValue).prod) = 87490457571481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_241
      · exact prime_fiftyAV_3025257869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 87490457571481) ^ 43745228785740 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 87490457571481) ^ 29163485857160 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 87490457571481) ^ 17498091514296 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 87490457571481) ^ 363030944280 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 87490457571481) ^ 28920 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_101408018718397 : Nat.Prime 101408018718397 := by
  apply lucas_primality 101408018718397 (2 : ZMod 101408018718397)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (650051402041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (650051402041, 1)] : List FactorBlock).map factorBlockValue).prod) = 101408018718397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_650051402041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101408018718397) ^ 50704009359198 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 101408018718397) ^ 33802672906132 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 101408018718397) ^ 7800616824492 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 101408018718397) ^ 156 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_135784093334783 : Nat.Prime 135784093334783 := by
  apply lucas_primality 135784093334783 (5 : ZMod 135784093334783)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67892046667391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67892046667391, 1)] : List FactorBlock).map factorBlockValue).prod) = 135784093334783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_67892046667391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 135784093334783) ^ 67892046667391 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 135784093334783) ^ 2 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_139452529777019 : Nat.Prime 139452529777019 := by
  apply lucas_primality 139452529777019 (2 : ZMod 139452529777019)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (3031576734283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (3031576734283, 1)] : List FactorBlock).map factorBlockValue).prod) = 139452529777019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_3031576734283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 139452529777019) ^ 69726264888509 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 139452529777019) ^ 6063153468566 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 139452529777019) ^ 46 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_158796207522221 : Nat.Prime 158796207522221 := by
  apply lucas_primality 158796207522221 (2 : ZMod 158796207522221)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (14431, 1), (32364193, 1)] : List FactorBlock).map factorBlockValue).prod) = 158796207522221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_14431
      · exact prime_fiftyAV_32364193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158796207522221) ^ 79398103761110 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 31759241504444 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 9340953383660 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 11003825620 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158796207522221) ^ 4906540 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_231922836591353 : Nat.Prime 231922836591353 := by
  apply lucas_primality 231922836591353 (3 : ZMod 231922836591353)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2833, 1), (40543, 1), (252401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2833, 1), (40543, 1), (252401, 1)] : List FactorBlock).map factorBlockValue).prod) = 231922836591353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_2833
      · exact prime_fiftyAV_40543
      · exact prime_fiftyAV_252401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 231922836591353) ^ 115961418295676 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 231922836591353) ^ 81864749944 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 231922836591353) ^ 5720416264 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 231922836591353) ^ 918866552 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_277074150678811 : Nat.Prime 277074150678811 := by
  apply lucas_primality 277074150678811 (2 : ZMod 277074150678811)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (131, 1), (810371591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (131, 1), (810371591, 1)] : List FactorBlock).map factorBlockValue).prod) = 277074150678811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_131
      · exact prime_fiftyAV_810371591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 277074150678811) ^ 138537075339405 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 277074150678811) ^ 92358050226270 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 277074150678811) ^ 55414830135762 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 277074150678811) ^ 9554281057890 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 277074150678811) ^ 2115069852510 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 277074150678811) ^ 341910 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_290907674250203 : Nat.Prime 290907674250203 := by
  apply lucas_primality 290907674250203 (2 : ZMod 290907674250203)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (116687, 1), (1246529923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (116687, 1), (1246529923, 1)] : List FactorBlock).map factorBlockValue).prod) = 290907674250203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_116687
      · exact prime_fiftyAV_1246529923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 290907674250203) ^ 145453837125101 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 290907674250203) ^ 2493059846 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 290907674250203) ^ 233374 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_296123742126743 : Nat.Prime 296123742126743 := by
  apply lucas_primality 296123742126743 (5 : ZMod 296123742126743)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (269, 1), (17755350889, 1)] : List FactorBlock).map factorBlockValue).prod) = 296123742126743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_269
      · exact prime_fiftyAV_17755350889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 296123742126743) ^ 148061871063371 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 9552378778282 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 1100831755118 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 296123742126743) ^ 16678 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_386519565736481 : Nat.Prime 386519565736481 := by
  apply lucas_primality 386519565736481 (3 : ZMod 386519565736481)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (219613389623, 1)] : List FactorBlock).map factorBlockValue).prod) = 386519565736481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_219613389623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 386519565736481) ^ 193259782868240 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 77303913147296 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 35138142339680 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 386519565736481) ^ 1760 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_397369741120927 : Nat.Prime 397369741120927 := by
  apply lucas_primality 397369741120927 (5 : ZMod 397369741120927)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (255707684119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (255707684119, 1)] : List FactorBlock).map factorBlockValue).prod) = 397369741120927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_255707684119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 397369741120927) ^ 198684870560463 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 397369741120927) ^ 132456580373642 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 397369741120927) ^ 56767105874418 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 397369741120927) ^ 10739722732998 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 397369741120927) ^ 1554 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_408130572867263 : Nat.Prime 408130572867263 := by
  apply lucas_primality 408130572867263 (7 : ZMod 408130572867263)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (101, 1), (941, 1), (2306261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (101, 1), (941, 1), (2306261, 1)] : List FactorBlock).map factorBlockValue).prod) = 408130572867263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_101
      · exact prime_fiftyAV_941
      · exact prime_fiftyAV_2306261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 408130572867263) ^ 204065286433631 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 408130572867263) ^ 58304367552466 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 408130572867263) ^ 21480556466698 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 408130572867263) ^ 4040896761062 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 408130572867263) ^ 433720056182 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 408130572867263) ^ 176966342 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_501028604968217 : Nat.Prime 501028604968217 := by
  apply lucas_primality 501028604968217 (3 : ZMod 501028604968217)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (79, 1), (6449, 1), (9456049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (79, 1), (6449, 1), (9456049, 1)] : List FactorBlock).map factorBlockValue).prod) = 501028604968217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_6449
      · exact prime_fiftyAV_9456049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 501028604968217) ^ 250514302484108 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 501028604968217) ^ 38540661920632 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 501028604968217) ^ 6342134240104 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 501028604968217) ^ 77690898584 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 501028604968217) ^ 52984984 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_537331870728673 : Nat.Prime 537331870728673 := by
  apply lucas_primality 537331870728673 (7 : ZMod 537331870728673)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5597206986757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5597206986757, 1)] : List FactorBlock).map factorBlockValue).prod) = 537331870728673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5597206986757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 537331870728673) ^ 268665935364336 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 537331870728673) ^ 179110623576224 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 537331870728673) ^ 96 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_596394404692817 : Nat.Prime 596394404692817 := by
  apply lucas_primality 596394404692817 (3 : ZMod 596394404692817)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2707, 1), (13769726743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2707, 1), (13769726743, 1)] : List FactorBlock).map factorBlockValue).prod) = 596394404692817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_2707
      · exact prime_fiftyAV_13769726743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 596394404692817) ^ 298197202346408 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 596394404692817) ^ 220315627888 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 596394404692817) ^ 43312 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_857580112926659 : Nat.Prime 857580112926659 := by
  apply lucas_primality 857580112926659 (2 : ZMod 857580112926659)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17209, 1), (46219, 1), (49009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17209, 1), (46219, 1), (49009, 1)] : List FactorBlock).map factorBlockValue).prod) = 857580112926659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_17209
      · exact prime_fiftyAV_46219
      · exact prime_fiftyAV_49009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 857580112926659) ^ 428790056463329 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 857580112926659) ^ 77961828447878 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 857580112926659) ^ 49833233362 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 857580112926659) ^ 18554709382 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 857580112926659) ^ 17498420962 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1093649152175339 : Nat.Prime 1093649152175339 := by
  apply lucas_primality 1093649152175339 (6 : ZMod 1093649152175339)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (223469, 1), (222452891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (223469, 1), (222452891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1093649152175339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_223469
      · exact prime_fiftyAV_222452891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1093649152175339) ^ 546824576087669 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093649152175339) ^ 99422650197758 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093649152175339) ^ 4893963602 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093649152175339) ^ 4916318 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1152234038950921 : Nat.Prime 1152234038950921 := by
  apply lucas_primality 1152234038950921 (14 : ZMod 1152234038950921)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (1066883369399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (1066883369399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152234038950921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_1066883369399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1152234038950921) ^ 576117019475460 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1152234038950921) ^ 384078012983640 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1152234038950921) ^ 230446807790184 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1152234038950921) ^ 1080 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1427064562026641 : Nat.Prime 1427064562026641 := by
  apply lucas_primality 1427064562026641 (7 : ZMod 1427064562026641)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (83, 1), (311, 1), (2521, 1), (274121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (83, 1), (311, 1), (2521, 1), (274121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1427064562026641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_83
      · exact prime_fiftyAV_311
      · exact prime_fiftyAV_2521
      · exact prime_fiftyAV_274121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1427064562026641) ^ 713532281013320 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427064562026641) ^ 285412912405328 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427064562026641) ^ 17193548940080 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427064562026641) ^ 4588632032240 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427064562026641) ^ 566070829840 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427064562026641) ^ 5205965840 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1508051471281241 : Nat.Prime 1508051471281241 := by
  apply lucas_primality 1508051471281241 (3 : ZMod 1508051471281241)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2333, 1), (16160002907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2333, 1), (16160002907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508051471281241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_2333
      · exact prime_fiftyAV_16160002907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1508051471281241) ^ 754025735640620 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508051471281241) ^ 301610294256248 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508051471281241) ^ 646400116280 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508051471281241) ^ 93320 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1748129962376687 : Nat.Prime 1748129962376687 := by
  apply lucas_primality 1748129962376687 (7 : ZMod 1748129962376687)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (73, 1), (137, 1), (49117, 1), (254197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (73, 1), (137, 1), (49117, 1), (254197, 1)] : List FactorBlock).map factorBlockValue).prod) = 1748129962376687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_73
      · exact prime_fiftyAV_137
      · exact prime_fiftyAV_49117
      · exact prime_fiftyAV_254197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1748129962376687) ^ 874064981188343 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1748129962376687) ^ 249732851768098 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1748129962376687) ^ 23946985785982 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1748129962376687) ^ 12760072718078 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1748129962376687) ^ 35591138758 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1748129962376687) ^ 6877067638 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1900977306686963 : Nat.Prime 1900977306686963 := by
  apply lucas_primality 1900977306686963 (2 : ZMod 1900977306686963)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (135784093334783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (135784093334783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1900977306686963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_135784093334783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1900977306686963) ^ 950488653343481 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1900977306686963) ^ 271568186669566 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1900977306686963) ^ 14 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1983855223395691 : Nat.Prime 1983855223395691 := by
  apply lucas_primality 1983855223395691 (2 : ZMod 1983855223395691)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (103, 1), (642024344141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (103, 1), (642024344141, 1)] : List FactorBlock).map factorBlockValue).prod) = 1983855223395691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_103
      · exact prime_fiftyAV_642024344141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1983855223395691) ^ 991927611697845 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983855223395691) ^ 661285074465230 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983855223395691) ^ 396771044679138 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983855223395691) ^ 19260730324230 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983855223395691) ^ 3090 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2797446213614389 : Nat.Prime 2797446213614389 := by
  apply lucas_primality 2797446213614389 (2 : ZMod 2797446213614389)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (589507, 1), (56492851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (589507, 1), (56492851, 1)] : List FactorBlock).map factorBlockValue).prod) = 2797446213614389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_589507
      · exact prime_fiftyAV_56492851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2797446213614389) ^ 1398723106807194 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2797446213614389) ^ 932482071204796 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2797446213614389) ^ 399635173373484 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2797446213614389) ^ 4745399484 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2797446213614389) ^ 49518588 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2820880298726107 : Nat.Prime 2820880298726107 := by
  apply lucas_primality 2820880298726107 (3 : ZMod 2820880298726107)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (1483112670203, 1)] : List FactorBlock).map factorBlockValue).prod) = 2820880298726107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_317
      · exact prime_fiftyAV_1483112670203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2820880298726107) ^ 1410440149363053 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 940293432908702 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 8898676021218 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2820880298726107) ^ 1902 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2996550152403179 : Nat.Prime 2996550152403179 := by
  apply lucas_primality 2996550152403179 (2 : ZMod 2996550152403179)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (31, 1), (79, 1), (65423, 1), (190843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (31, 1), (79, 1), (65423, 1), (190843, 1)] : List FactorBlock).map factorBlockValue).prod) = 2996550152403179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_65423
      · exact prime_fiftyAV_190843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2996550152403179) ^ 1498275076201589 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2996550152403179) ^ 428078593200454 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2996550152403179) ^ 96662908142038 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2996550152403179) ^ 37931014587382 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2996550152403179) ^ 45802701686 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2996550152403179) ^ 15701650846 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_3593722313513149 : Nat.Prime 3593722313513149 := by
  apply lucas_primality 3593722313513149 (6 : ZMod 3593722313513149)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (512713, 1), (5358737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (512713, 1), (5358737, 1)] : List FactorBlock).map factorBlockValue).prod) = 3593722313513149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_109
      · exact prime_fiftyAV_512713
      · exact prime_fiftyAV_5358737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3593722313513149) ^ 1796861156756574 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3593722313513149) ^ 1197907437837716 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3593722313513149) ^ 32969929481772 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3593722313513149) ^ 7009227996 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3593722313513149) ^ 670628604 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_5523140549247743 : Nat.Prime 5523140549247743 := by
  apply lucas_primality 5523140549247743 (5 : ZMod 5523140549247743)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 2), (101, 1), (463, 1), (631, 1), (97387, 1)] : List FactorBlock).map factorBlockValue).prod) = 5523140549247743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_101
      · exact prime_fiftyAV_463
      · exact prime_fiftyAV_631
      · exact prime_fiftyAV_97387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5523140549247743) ^ 2761570274623871 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 178165824169282 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 54684559893542 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 11929029264034 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 8752996116082 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 5523140549247743) ^ 56713324666 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_11390813889425209 : Nat.Prime 11390813889425209 := by
  apply lucas_primality 11390813889425209 (17 : ZMod 11390813889425209)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (23, 1), (2377, 1), (413396887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (23, 1), (2377, 1), (413396887, 1)] : List FactorBlock).map factorBlockValue).prod) = 11390813889425209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_2377
      · exact prime_fiftyAV_413396887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 11390813889425209) ^ 5695406944712604 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 11390813889425209) ^ 3796937963141736 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 11390813889425209) ^ 1627259127060744 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 11390813889425209) ^ 495252777801096 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 11390813889425209) ^ 4792096714104 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 11390813889425209) ^ 27554184 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_12866222659007413 : Nat.Prime 12866222659007413 := by
  apply lucas_primality 12866222659007413 (2 : ZMod 12866222659007413)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (67, 1), (242819, 1), (1292237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (67, 1), (242819, 1), (1292237, 1)] : List FactorBlock).map factorBlockValue).prod) = 12866222659007413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_67
      · exact prime_fiftyAV_242819
      · exact prime_fiftyAV_1292237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12866222659007413) ^ 6433111329503706 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 4288740886335804 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 756836627000436 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 192033174015036 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 52986885948 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12866222659007413) ^ 9956550276 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_20337598823458661 : Nat.Prime 20337598823458661 := by
  apply lucas_primality 20337598823458661 (2 : ZMod 20337598823458661)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4013, 1), (253396446841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4013, 1), (253396446841, 1)] : List FactorBlock).map factorBlockValue).prod) = 20337598823458661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_4013
      · exact prime_fiftyAV_253396446841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20337598823458661) ^ 10168799411729330 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20337598823458661) ^ 4067519764691732 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20337598823458661) ^ 5067928936820 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20337598823458661) ^ 80260 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_20406528643363151 : Nat.Prime 20406528643363151 := by
  apply lucas_primality 20406528643363151 (7 : ZMod 20406528643363151)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (408130572867263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (408130572867263, 1)] : List FactorBlock).map factorBlockValue).prod) = 20406528643363151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_408130572867263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 20406528643363151) ^ 10203264321681575 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20406528643363151) ^ 4081305728672630 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20406528643363151) ^ 50 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_21430121685966821 : Nat.Prime 21430121685966821 := by
  apply lucas_primality 21430121685966821 (2 : ZMod 21430121685966821)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1877, 1), (5479, 1), (104190727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1877, 1), (5479, 1), (104190727, 1)] : List FactorBlock).map factorBlockValue).prod) = 21430121685966821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_1877
      · exact prime_fiftyAV_5479
      · exact prime_fiftyAV_104190727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21430121685966821) ^ 10715060842983410 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21430121685966821) ^ 4286024337193364 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21430121685966821) ^ 11417219864660 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21430121685966821) ^ 3911319891580 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21430121685966821) ^ 205681660 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_22540789770483337 : Nat.Prime 22540789770483337 := by
  apply lucas_primality 22540789770483337 (5 : ZMod 22540789770483337)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (8590367, 1), (9939247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (8590367, 1), (9939247, 1)] : List FactorBlock).map factorBlockValue).prod) = 22540789770483337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_8590367
      · exact prime_fiftyAV_9939247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22540789770483337) ^ 11270394885241668 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 22540789770483337) ^ 7513596590161112 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 22540789770483337) ^ 2049162706407576 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 22540789770483337) ^ 2623961208 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 22540789770483337) ^ 2267856888 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_25592998416424177 : Nat.Prime 25592998416424177 := by
  apply lucas_primality 25592998416424177 (5 : ZMod 25592998416424177)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (656951, 1), (42716273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25592998416424177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_656951
      · exact prime_fiftyAV_42716273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25592998416424177) ^ 12796499208212088 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 8530999472141392 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 1346999916653904 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 38957240976 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 25592998416424177) ^ 599139312 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_28583317353999781 : Nat.Prime 28583317353999781 := by
  apply lucas_primality 28583317353999781 (2 : ZMod 28583317353999781)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (158796207522221, 1)] : List FactorBlock).map factorBlockValue).prod) = 28583317353999781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_158796207522221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28583317353999781) ^ 14291658676999890 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 9527772451333260 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 5716663470799956 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28583317353999781) ^ 180 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_30354743159973073 : Nat.Prime 30354743159973073 := by
  apply lucas_primality 30354743159973073 (5 : ZMod 30354743159973073)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (37, 1), (163, 1), (4157, 1), (8408039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (37, 1), (163, 1), (4157, 1), (8408039, 1)] : List FactorBlock).map factorBlockValue).prod) = 30354743159973073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_163
      · exact prime_fiftyAV_4157
      · exact prime_fiftyAV_8408039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30354743159973073) ^ 15177371579986536 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 10118247719991024 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 820398463783056 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 186225418159344 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 7302079182096 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30354743159973073) ^ 3610204848 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_47261873941684471 : Nat.Prime 47261873941684471 := by
  apply lucas_primality 47261873941684471 (19 : ZMod 47261873941684471)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (443, 1), (1185399396581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (443, 1), (1185399396581, 1)] : List FactorBlock).map factorBlockValue).prod) = 47261873941684471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_443
      · exact prime_fiftyAV_1185399396581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 47261873941684471) ^ 23630936970842235 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (19 : ZMod 47261873941684471) ^ 15753957980561490 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (19 : ZMod 47261873941684471) ^ 9452374788336894 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (19 : ZMod 47261873941684471) ^ 106685945692290 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (19 : ZMod 47261873941684471) ^ 39870 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_50375378072400611 : Nat.Prime 50375378072400611 := by
  apply lucas_primality 50375378072400611 (2 : ZMod 50375378072400611)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (70951236721691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (70951236721691, 1)] : List FactorBlock).map factorBlockValue).prod) = 50375378072400611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_71
      · exact prime_fiftyAV_70951236721691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50375378072400611) ^ 25187689036200305 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50375378072400611) ^ 10075075614480122 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50375378072400611) ^ 709512367216910 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50375378072400611) ^ 710 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_58810721685897197 : Nat.Prime 58810721685897197 := by
  apply lucas_primality 58810721685897197 (2 : ZMod 58810721685897197)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (397369741120927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (397369741120927, 1)] : List FactorBlock).map factorBlockValue).prod) = 58810721685897197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_397369741120927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58810721685897197) ^ 29405360842948598 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58810721685897197) ^ 1589478964483708 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 58810721685897197) ^ 148 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_66576822500643073 : Nat.Prime 66576822500643073 := by
  apply lucas_primality 66576822500643073 (5 : ZMod 66576822500643073)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5099327703787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66576822500643073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_5099327703787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66576822500643073) ^ 33288411250321536 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 22192274166881024 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 3916283676508416 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 66576822500643073) ^ 13056 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_263832006990285737 : Nat.Prime 263832006990285737 := by
  apply lucas_primality 263832006990285737 (3 : ZMod 263832006990285737)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3209, 1), (41467, 1), (247836439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3209, 1), (41467, 1), (247836439, 1)] : List FactorBlock).map factorBlockValue).prod) = 263832006990285737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3209
      · exact prime_fiftyAV_41467
      · exact prime_fiftyAV_247836439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 263832006990285737) ^ 131916003495142868 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 263832006990285737) ^ 82216268928104 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 263832006990285737) ^ 6362457062008 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 263832006990285737) ^ 1064540824 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_284239899442134347 : Nat.Prime 284239899442134347 := by
  apply lucas_primality 284239899442134347 (2 : ZMod 284239899442134347)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (83, 1), (74447328298097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (83, 1), (74447328298097, 1)] : List FactorBlock).map factorBlockValue).prod) = 284239899442134347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_83
      · exact prime_fiftyAV_74447328298097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 284239899442134347) ^ 142119949721067173 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 284239899442134347) ^ 12358256497484102 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 284239899442134347) ^ 3424577101712462 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 284239899442134347) ^ 3818 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_291040469490094697 : Nat.Prime 291040469490094697 := by
  apply lucas_primality 291040469490094697 (3 : ZMod 291040469490094697)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (596394404692817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (596394404692817, 1)] : List FactorBlock).map factorBlockValue).prod) = 291040469490094697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_61
      · exact prime_fiftyAV_596394404692817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 291040469490094697) ^ 145520234745047348 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 291040469490094697) ^ 4771155237542536 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 291040469490094697) ^ 488 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_364775017097087249 : Nat.Prime 364775017097087249 := by
  apply lucas_primality 364775017097087249 (3 : ZMod 364775017097087249)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (241, 2), (4861, 1), (80750533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (241, 2), (4861, 1), (80750533, 1)] : List FactorBlock).map factorBlockValue).prod) = 364775017097087249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_241
      · exact prime_fiftyAV_4861
      · exact prime_fiftyAV_80750533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 364775017097087249) ^ 182387508548543624 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 364775017097087249) ^ 1513589282560528 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 364775017097087249) ^ 75041147314768 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 364775017097087249) ^ 4517307856 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_515106966899852879 : Nat.Prime 515106966899852879 := by
  apply lucas_primality 515106966899852879 (13 : ZMod 515106966899852879)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (401, 1), (1249, 1), (2151605849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (401, 1), (1249, 1), (2151605849, 1)] : List FactorBlock).map factorBlockValue).prod) = 515106966899852879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_239
      · exact prime_fiftyAV_401
      · exact prime_fiftyAV_1249
      · exact prime_fiftyAV_2151605849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 515106966899852879) ^ 257553483449926439 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 515106966899852879) ^ 2155259275731602 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 515106966899852879) ^ 1284556027181678 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 515106966899852879) ^ 412415505924622 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (13 : ZMod 515106966899852879) ^ 239405822 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_61717
      · exact prime_fiftyAV_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2554031246879972731 : Nat.Prime 2554031246879972731 := by
  apply lucas_primality 2554031246879972731 (3 : ZMod 2554031246879972731)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (59, 1), (79, 1), (1405019967587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (59, 1), (79, 1), (1405019967587, 1)] : List FactorBlock).map factorBlockValue).prod) = 2554031246879972731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_79
      · exact prime_fiftyAV_1405019967587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2554031246879972731) ^ 1277015623439986365 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 851343748959990910 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 510806249375994546 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 196463942067690210 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 43288665201355470 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 32329509454176870 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2554031246879972731) ^ 1817790 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_439
      · exact prime_fiftyAV_853
      · exact prime_fiftyAV_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_8538352360051590607 : Nat.Prime 8538352360051590607 := by
  apply lucas_primality 8538352360051590607 (3 : ZMod 8538352360051590607)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14033, 1), (101408018718397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14033, 1), (101408018718397, 1)] : List FactorBlock).map factorBlockValue).prod) = 8538352360051590607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_14033
      · exact prime_fiftyAV_101408018718397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8538352360051590607) ^ 4269176180025795303 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8538352360051590607) ^ 2846117453350530202 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8538352360051590607) ^ 608448112310382 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8538352360051590607) ^ 84198 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_41387675792410698833 : Nat.Prime 41387675792410698833 := by
  apply lucas_primality 41387675792410698833 (3 : ZMod 41387675792410698833)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (66533, 1), (5592011, 1), (6952579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (66533, 1), (5592011, 1), (6952579, 1)] : List FactorBlock).map factorBlockValue).prod) = 41387675792410698833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_66533
      · exact prime_fiftyAV_5592011
      · exact prime_fiftyAV_6952579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41387675792410698833) ^ 20693837896205349416 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 41387675792410698833) ^ 622062371941904 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 41387675792410698833) ^ 7401215017712 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 41387675792410698833) ^ 5952852285808 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_97390555111845758233 : Nat.Prime 97390555111845758233 := by
  apply lucas_primality 97390555111845758233 (5 : ZMod 97390555111845758233)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (23, 1), (58810721685897197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (23, 1), (58810721685897197, 1)] : List FactorBlock).map factorBlockValue).prod) = 97390555111845758233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_58810721685897197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 97390555111845758233) ^ 48695277555922879116 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 97390555111845758233) ^ 32463518370615252744 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 97390555111845758233) ^ 4234371961384598184 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 97390555111845758233) ^ 1656 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_318698601733276800961 : Nat.Prime 318698601733276800961 := by
  apply lucas_primality 318698601733276800961 (11 : ZMod 318698601733276800961)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (10687, 1), (939487, 1), (33064529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (10687, 1), (939487, 1), (33064529, 1)] : List FactorBlock).map factorBlockValue).prod) = 318698601733276800961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_10687
      · exact prime_fiftyAV_939487
      · exact prime_fiftyAV_33064529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 318698601733276800961) ^ 159349300866638400480 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 106232867244425600320 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 63739720346655360192 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 29821147350358080 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 339226196566080 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 318698601733276800961) ^ 9638685666240 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_474232053920584667009 : Nat.Prime 474232053920584667009 := by
  apply lucas_primality 474232053920584667009 (3 : ZMod 474232053920584667009)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (17027, 1), (31084562512099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (17027, 1), (31084562512099, 1)] : List FactorBlock).map factorBlockValue).prod) = 474232053920584667009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_17027
      · exact prime_fiftyAV_31084562512099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 474232053920584667009) ^ 237116026960292333504 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 474232053920584667009) ^ 67747436274369238144 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 474232053920584667009) ^ 27851768010840704 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 474232053920584667009) ^ 15256192 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1999142903039753380243 : Nat.Prime 1999142903039753380243 := by
  apply lucas_primality 1999142903039753380243 (3 : ZMod 1999142903039753380243)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (248944687, 1), (1338411708461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (248944687, 1), (1338411708461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1999142903039753380243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_248944687
      · exact prime_fiftyAV_1338411708461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1999142903039753380243) ^ 999571451519876690121 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1999142903039753380243) ^ 666380967679917793414 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1999142903039753380243) ^ 8030470250766 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1999142903039753380243) ^ 1493668122 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_107
      · exact prime_fiftyAV_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_3636586369677809254799 : Nat.Prime 3636586369677809254799 := by
  apply lucas_primality 3636586369677809254799 (7 : ZMod 3636586369677809254799)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (1553, 1), (12866222659007413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (1553, 1), (12866222659007413, 1)] : List FactorBlock).map factorBlockValue).prod) = 3636586369677809254799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_1553
      · exact prime_fiftyAV_12866222659007413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3636586369677809254799) ^ 1818293184838904627399 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3636586369677809254799) ^ 519512338525401322114 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3636586369677809254799) ^ 279737413052139173446 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3636586369677809254799) ^ 2341652523939349166 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3636586369677809254799) ^ 282646 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_5017116660004810029623 : Nat.Prime 5017116660004810029623 := by
  apply lucas_primality 5017116660004810029623 (5 : ZMod 5017116660004810029623)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (698039, 1), (3593722313513149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (698039, 1), (3593722313513149, 1)] : List FactorBlock).map factorBlockValue).prod) = 5017116660004810029623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_698039
      · exact prime_fiftyAV_3593722313513149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5017116660004810029623) ^ 2508558330002405014811 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 5017116660004810029623) ^ 7187444627026298 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 5017116660004810029623) ^ 1396078 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_6891984566505300835487 : Nat.Prime 6891984566505300835487 := by
  apply lucas_primality 6891984566505300835487 (5 : ZMod 6891984566505300835487)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11637001, 1), (296123742126743, 1)] : List FactorBlock).map factorBlockValue).prod) = 6891984566505300835487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_11637001
      · exact prime_fiftyAV_296123742126743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6891984566505300835487) ^ 3445992283252650417743 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 592247484253486 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6891984566505300835487) ^ 23274002 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_8225623448496833693393 : Nat.Prime 8225623448496833693393 := by
  apply lucas_primality 8225623448496833693393 (3 : ZMod 8225623448496833693393)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (1231, 1), (101501, 1), (316502478779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (1231, 1), (101501, 1), (316502478779, 1)] : List FactorBlock).map factorBlockValue).prod) = 8225623448496833693393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_1231
      · exact prime_fiftyAV_101501
      · exact prime_fiftyAV_316502478779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8225623448496833693393) ^ 4112811724248416846696 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8225623448496833693393) ^ 632740265268987207184 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8225623448496833693393) ^ 6682066164497834032 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8225623448496833693393) ^ 81039826686405392 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 8225623448496833693393) ^ 25989128048 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_14031086011350298342633 : Nat.Prime 14031086011350298342633 := by
  apply lucas_primality 14031086011350298342633 (5 : ZMod 14031086011350298342633)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (50906021, 1), (3828156095761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (50906021, 1), (3828156095761, 1)] : List FactorBlock).map factorBlockValue).prod) = 14031086011350298342633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_50906021
      · exact prime_fiftyAV_3828156095761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14031086011350298342633) ^ 7015543005675149171316 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 14031086011350298342633) ^ 4677028670450099447544 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 14031086011350298342633) ^ 275627238894792 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 14031086011350298342633) ^ 3665233512 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_16451246896993667386787 : Nat.Prime 16451246896993667386787 := by
  apply lucas_primality 16451246896993667386787 (2 : ZMod 16451246896993667386787)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8225623448496833693393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8225623448496833693393, 1)] : List FactorBlock).map factorBlockValue).prod) = 16451246896993667386787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_8225623448496833693393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 16451246896993667386787) ^ 8225623448496833693393 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16451246896993667386787) ^ 2 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_53936369638161461788703 : Nat.Prime 53936369638161461788703 := by
  apply lucas_primality 53936369638161461788703 (5 : ZMod 53936369638161461788703)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (10126309, 1), (50248681511863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (10126309, 1), (50248681511863, 1)] : List FactorBlock).map factorBlockValue).prod) = 53936369638161461788703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_10126309
      · exact prime_fiftyAV_50248681511863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53936369638161461788703) ^ 26968184819080730894351 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 53936369638161461788703) ^ 1017667351663423807334 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 53936369638161461788703) ^ 5326360240257478 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 53936369638161461788703) ^ 1073388754 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_58198922731188676884361 : Nat.Prime 58198922731188676884361 := by
  apply lucas_primality 58198922731188676884361 (7 : ZMod 58198922731188676884361)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (7929133, 1), (2659378548317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (7929133, 1), (2659378548317, 1)] : List FactorBlock).map factorBlockValue).prod) = 58198922731188676884361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_7929133
      · exact prime_fiftyAV_2659378548317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 58198922731188676884361) ^ 29099461365594338442180 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 19399640910396225628120 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 11639784546237735376872 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 2530387944834290299320 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 7339884793354920 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58198922731188676884361) ^ 21884407080 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_75772932744131311864783 : Nat.Prime 75772932744131311864783 := by
  apply lucas_primality 75772932744131311864783 (3 : ZMod 75772932744131311864783)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (127, 1), (163, 1), (160423, 1), (122671363769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (127, 1), (163, 1), (160423, 1), (122671363769, 1)] : List FactorBlock).map factorBlockValue).prod) = 75772932744131311864783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_127
      · exact prime_fiftyAV_163
      · exact prime_fiftyAV_160423
      · exact prime_fiftyAV_122671363769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75772932744131311864783) ^ 37886466372065655932391 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 25257644248043770621594 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 2444288153036493931122 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 596637265701821353266 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 464864618062155287514 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 472332101657064834 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (3 : ZMod 75772932744131311864783) ^ 617690473278 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_194932066852676869575263 : Nat.Prime 194932066852676869575263 := by
  apply lucas_primality 194932066852676869575263 (5 : ZMod 194932066852676869575263)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (156539, 1), (196453, 1), (243797203261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (156539, 1), (196453, 1), (243797203261, 1)] : List FactorBlock).map factorBlockValue).prod) = 194932066852676869575263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_156539
      · exact prime_fiftyAV_196453
      · exact prime_fiftyAV_243797203261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 194932066852676869575263) ^ 97466033426338434787631 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 194932066852676869575263) ^ 14994774373282836121174 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 194932066852676869575263) ^ 1245261991278064058 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 194932066852676869575263) ^ 992258030433115654 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (5 : ZMod 194932066852676869575263) ^ 799566460342 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_197526445210116395256319 : Nat.Prime 197526445210116395256319 := by
  apply lucas_primality 197526445210116395256319 (17 : ZMod 197526445210116395256319)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30890258779, 1), (1065742907407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30890258779, 1), (1065742907407, 1)] : List FactorBlock).map factorBlockValue).prod) = 197526445210116395256319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_30890258779
      · exact prime_fiftyAV_1065742907407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 197526445210116395256319) ^ 98763222605058197628159 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 197526445210116395256319) ^ 65842148403372131752106 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 197526445210116395256319) ^ 6394457444442 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (17 : ZMod 197526445210116395256319) ^ 185341552674 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_668143682947997302886363 : Nat.Prime 668143682947997302886363 := by
  apply lucas_primality 668143682947997302886363 (2 : ZMod 668143682947997302886363)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (16937033, 1), (857580112926659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (16937033, 1), (857580112926659, 1)] : List FactorBlock).map factorBlockValue).prod) = 668143682947997302886363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_16937033
      · exact prime_fiftyAV_857580112926659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 668143682947997302886363) ^ 334071841473998651443181 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 668143682947997302886363) ^ 29049725345565100125494 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 668143682947997302886363) ^ 39448685194626314 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 668143682947997302886363) ^ 779103518 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_782636853810238357436921 : Nat.Prime 782636853810238357436921 := by
  apply lucas_primality 782636853810238357436921 (11 : ZMod 782636853810238357436921)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37, 1), (104527, 1), (3558407, 1), (1421721311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37, 1), (104527, 1), (3558407, 1), (1421721311, 1)] : List FactorBlock).map factorBlockValue).prod) = 782636853810238357436921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_104527
      · exact prime_fiftyAV_3558407
      · exact prime_fiftyAV_1421721311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 782636853810238357436921) ^ 391318426905119178718460 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 782636853810238357436921) ^ 156527370762047671487384 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 782636853810238357436921) ^ 21152347400276712363160 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 782636853810238357436921) ^ 7487413336365133960 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 782636853810238357436921) ^ 219940229942847560 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 782636853810238357436921) ^ 550485420563720 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_4540544143570252198753213 : Nat.Prime 4540544143570252198753213 := by
  apply lucas_primality 4540544143570252198753213 (2 : ZMod 4540544143570252198753213)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (16451246896993667386787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (16451246896993667386787, 1)] : List FactorBlock).map factorBlockValue).prod) = 4540544143570252198753213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_16451246896993667386787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4540544143570252198753213) ^ 2270272071785126099376606 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4540544143570252198753213) ^ 1513514714523417399584404 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4540544143570252198753213) ^ 197414962763924008641444 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4540544143570252198753213) ^ 276 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_6269312143932666600442049 : Nat.Prime 6269312143932666600442049 := by
  apply lucas_primality 6269312143932666600442049 (6 : ZMod 6269312143932666600442049)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 2), (1999142903039753380243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 2), (1999142903039753380243, 1)] : List FactorBlock).map factorBlockValue).prod) = 6269312143932666600442049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_1999142903039753380243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 6269312143932666600442049) ^ 3134656071966333300221024 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6269312143932666600442049) ^ 895616020561809514348864 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6269312143932666600442049) ^ 3136 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_10666428041346285343841227 : Nat.Prime 10666428041346285343841227 := by
  apply lucas_primality 10666428041346285343841227 (2 : ZMod 10666428041346285343841227)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (197526445210116395256319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (197526445210116395256319, 1)] : List FactorBlock).map factorBlockValue).prod) = 10666428041346285343841227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_197526445210116395256319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10666428041346285343841227) ^ 5333214020673142671920613 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 10666428041346285343841227) ^ 3555476013782095114613742 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 10666428041346285343841227) ^ 54 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_35376028848079660906982693 : Nat.Prime 35376028848079660906982693 := by
  apply lucas_primality 35376028848079660906982693 (2 : ZMod 35376028848079660906982693)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (1907, 1), (104003, 1), (501028604968217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (1907, 1), (104003, 1), (501028604968217, 1)] : List FactorBlock).map factorBlockValue).prod) = 35376028848079660906982693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_89
      · exact prime_fiftyAV_1907
      · exact prime_fiftyAV_104003
      · exact prime_fiftyAV_501028604968217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35376028848079660906982693) ^ 17688014424039830453491346 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 35376028848079660906982693) ^ 397483470203142257381828 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 35376028848079660906982693) ^ 18550618168893372263756 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 35376028848079660906982693) ^ 340144311684082775564 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 35376028848079660906982693) ^ 70606804676 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_49302205342069318912066789 : Nat.Prime 49302205342069318912066789 := by
  apply lucas_primality 49302205342069318912066789 (2 : ZMod 49302205342069318912066789)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (419, 1), (421, 1), (99347, 1), (8683013175229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (419, 1), (421, 1), (99347, 1), (8683013175229, 1)] : List FactorBlock).map factorBlockValue).prod) = 49302205342069318912066789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_419
      · exact prime_fiftyAV_421
      · exact prime_fiftyAV_99347
      · exact prime_fiftyAV_8683013175229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49302205342069318912066789) ^ 24651102671034659456033394 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49302205342069318912066789) ^ 16434068447356439637355596 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49302205342069318912066789) ^ 117666361198256131055052 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49302205342069318912066789) ^ 117107376109428310955028 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49302205342069318912066789) ^ 496262648515499400204 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49302205342069318912066789) ^ 5678006510772 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_75016934270483646415695533 : Nat.Prime 75016934270483646415695533 := by
  apply lucas_primality 75016934270483646415695533 (2 : ZMod 75016934270483646415695533)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (277, 1), (541, 1), (2554031246879972731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (277, 1), (541, 1), (2554031246879972731, 1)] : List FactorBlock).map factorBlockValue).prod) = 75016934270483646415695533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_277
      · exact prime_fiftyAV_541
      · exact prime_fiftyAV_2554031246879972731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 75016934270483646415695533) ^ 37508467135241823207847766 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75016934270483646415695533) ^ 10716704895783378059385076 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75016934270483646415695533) ^ 270819257294164788504316 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75016934270483646415695533) ^ 138663464455607479511452 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75016934270483646415695533) ^ 29371972 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_425275857590943261694734389 : Nat.Prime 425275857590943261694734389 := by
  apply lucas_primality 425275857590943261694734389 (2 : ZMod 425275857590943261694734389)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23704693, 1), (263832006990285737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23704693, 1), (263832006990285737, 1)] : List FactorBlock).map factorBlockValue).prod) = 425275857590943261694734389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_23704693
      · exact prime_fiftyAV_263832006990285737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 425275857590943261694734389) ^ 212637928795471630847367194 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425275857590943261694734389) ^ 25016226917114309511454964 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425275857590943261694734389) ^ 17940576475339430116 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425275857590943261694734389) ^ 1611919124 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_628865363884479929527320001 : Nat.Prime 628865363884479929527320001 := by
  apply lucas_primality 628865363884479929527320001 (97 : ZMod 628865363884479929527320001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 628865363884479929527320001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 628865363884479929527320001) ^ 314432681942239964763660000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 209621787961493309842440000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 125773072776895985905464000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 89837909126354275646760000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 57169578534952720866120000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 48374258760344609963640000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 36992080228498819383960000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 33098177046551575238280000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 27341972342803475196840000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 21685012547740687225080000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 20285979480144513855720000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 16996361186067025122360000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 15338179606938534866520000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 14624775904290230919240000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 11865384224235470368440000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 10658734981092880161480000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (97 : ZMod 628865363884479929527320001) ^ 10309268260401310320120000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_635627357044528100812560001 : Nat.Prime 635627357044528100812560001 := by
  apply lucas_primality 635627357044528100812560001 (71 : ZMod 635627357044528100812560001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 635627357044528100812560001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 635627357044528100812560001) ^ 317813678522264050406280000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 211875785681509366937520000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 127125471408905620162512000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 90803908149218300116080000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 57784305185866190982960000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 48894412080348315447120000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 37389844532031064753680000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 33454071423396215832240000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 27635972045414265252720000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 21918184725673382786640000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 17179117757960218940880000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 15503106269378734166160000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 14782031559175072111920000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 13523986320096342570480000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 11992969000840152845520000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 10773345034653018657840000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 635627357044528100812560001) ^ 10420120607287345914960000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_729794372902976708340346667 : Nat.Prime 729794372902976708340346667 := by
  apply lucas_primality 729794372902976708340346667 (2 : ZMod 729794372902976708340346667)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1000334917, 1), (364775017097087249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1000334917, 1), (364775017097087249, 1)] : List FactorBlock).map factorBlockValue).prod) = 729794372902976708340346667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_1000334917
      · exact prime_fiftyAV_364775017097087249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 729794372902976708340346667) ^ 364897186451488354170173333 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 729794372902976708340346667) ^ 729550034194174498 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (2 : ZMod 729794372902976708340346667) ^ 2000669834 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_757863387245398889430360001 : Nat.Prime 757863387245398889430360001 := by
  apply lucas_primality 757863387245398889430360001 (26 : ZMod 757863387245398889430360001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 4), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 4), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 757863387245398889430360001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 757863387245398889430360001) ^ 378931693622699444715180000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 252621129081799629810120000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 151572677449079777886072000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 108266198177914127061480000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 68896671567763535402760000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 44580199249729346437080000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 39887546697126257338440000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 32950582054147777801320000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 26133220249841341014840000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 24447206040174157723560000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 20482794249875645660280000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 18484472859643875351960000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 17624729935939509056520000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 16124752920114869987880000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 14299309193309413008120000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 12845142156701676092040000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 757863387245398889430360001) ^ 12423989954842604744760000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_909436064694478667316432001 : Nat.Prime 909436064694478667316432001 := by
  apply lucas_primality 909436064694478667316432001 (26 : ZMod 909436064694478667316432001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478667316432001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 909436064694478667316432001) ^ 454718032347239333658216000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 303145354898159555772144000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 181887212938895733463286400 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 129919437813496952473776000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 82676005881316242483312000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 53496239099675215724496000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 47865056036551508806128000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 39540698464977333361584000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 31359864299809609217808000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 29336647248208989268272000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 24579353099850774792336000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 22181367431572650422352000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 21149675923127410867824000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 19349703504137843985456000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 17159171031971295609744000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 15414170588042011310448000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (26 : ZMod 909436064694478667316432001) ^ 14908787945811125693712000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_969071216477723170091280001 : Nat.Prime 969071216477723170091280001 := by
  apply lucas_primality 969071216477723170091280001 (103 : ZMod 969071216477723170091280001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 969071216477723170091280001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 969071216477723170091280001) ^ 484535608238861585045640000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 323023738825907723363760000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 193814243295544634018256000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 138438745211103310013040000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 88097383316156651826480000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 74543939729055628468560000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 57004189204571951181840000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 51003748235669640531120000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 42133531151205355221360000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 33416248844059419658320000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 31260361821862037744880000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 26191113958857382975440000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 23635883328724955368080000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 22536539918086585350960000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 20618536520802620640240000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 18284362575051380567760000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (103 : ZMod 969071216477723170091280001) ^ 16424935872503782543920000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1074788076457111152283056001 : Nat.Prime 1074788076457111152283056001 := by
  apply lucas_primality 1074788076457111152283056001 (67 : ZMod 1074788076457111152283056001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 3), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1074788076457111152283056001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1074788076457111152283056001) ^ 537394038228555576141528000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 358262692152370384094352000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 214957615291422230456611200 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 153541153779587307469008000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 82676005881316242483312000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 63222828026888891310768000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 56567793497742692225424000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 46729916367700484881872000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 37061657808865901802864000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 34670583111519714589776000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 29048326390732733845488000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 26214343328222223226416000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 24995071545514212843792000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 22867831413981088346448000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 20279020310511531175152000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 18216747058595104275984000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (67 : ZMod 1074788076457111152283056001) ^ 17619476663231330365296000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1477833605128527834389202001 : Nat.Prime 1477833605128527834389202001 := by
  apply lucas_primality 1477833605128527834389202001 (107 : ZMod 1477833605128527834389202001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477833605128527834389202001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1477833605128527834389202001) ^ 738916802564263917194601000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 492611201709509278129734000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 295566721025705566877840400 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 211119086446932547769886000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 134348509557138894035382000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 113679508086809833414554000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 86931388536972225552306000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 77780716059396201809958000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 64253635005588166712574000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 50959779487190614978938000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 47672051778339607560942000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 39941448787257509037546000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 36044722076305556936322000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 34368223375082042660214000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 31443268194223996476366000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 27883652926953355365834000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 25048027205568268379478000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (107 : ZMod 1477833605128527834389202001) ^ 24226780411943079252282000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1642037339031697593765780001 : Nat.Prime 1642037339031697593765780001 := by
  apply lucas_primality 1642037339031697593765780001 (71 : ZMod 1642037339031697593765780001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1642037339031697593765780001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 1642037339031697593765780001) ^ 821018669515848796882890000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 547345779677232531255260000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 328407467806339518753156000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 234576762718813941966540000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 149276121730154326705980000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 126310564540899814905060000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 96590431707746917280340000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 86423017843773557566620000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 71392927783986851902860000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 56621977207989572198820000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 52968946420377341734380000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 44379387541397232263940000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 40049691195895063262580000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 38186914861202269622460000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 34936964660248884973740000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 30981836585503728184260000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 27831141339520298199420000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (71 : ZMod 1642037339031697593765780001) ^ 26918644902158976946980000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_1791313460761851920471760001 : Nat.Prime 1791313460761851920471760001 := by
  apply lucas_primality 1791313460761851920471760001 (11 : ZMod 1791313460761851920471760001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 4), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 4), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1791313460761851920471760001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1791313460761851920471760001) ^ 895656730380925960235880000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 597104486920617306823920000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 358262692152370384094352000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 255901922965978845781680000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 137793343135527070805520000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 105371380044814818851280000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 94279655829571153709040000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 77883193946167474803120000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 61769429681443169671440000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 57784305185866190982960000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 48413877317887889742480000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 43690572213703705377360000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 41658452575857021406320000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 38113052356635147244080000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 33798367184185885291920000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 30361245097658507126640000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1791313460761851920471760001) ^ 29365794438718883942160000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_2686970191142777880707640001 : Nat.Prime 2686970191142777880707640001 := by
  apply lucas_primality 2686970191142777880707640001 (83 : ZMod 2686970191142777880707640001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 4), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 4), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2686970191142777880707640001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 2686970191142777880707640001) ^ 1343485095571388940353820000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 895656730380925960235880000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 537394038228555576141528000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 383852884448968268672520000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 206690014703290606208280000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 158057070067222228276920000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 141419483744356730563560000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 116824790919251212204680000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 92654144522164754507160000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 86676457778799286474440000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 72620815976831834613720000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 65535858320555558066040000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 62487678863785532109480000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 57169578534952720866120000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 50697550776278827937880000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 45541867646487760689960000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (83 : ZMod 2686970191142777880707640001) ^ 44048691658078325913240000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_4926112017095092781297340001 : Nat.Prime 4926112017095092781297340001 := by
  apply lucas_primality 4926112017095092781297340001 (101 : ZMod 4926112017095092781297340001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 4926112017095092781297340001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 4926112017095092781297340001) ^ 2463056008547546390648670000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 1642037339031697593765780000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 985222403419018556259468000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 703730288156441825899620000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 447828365190462980117940000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 378931693622699444715180000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 289771295123240751841020000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 259269053531320672699860000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 214178783351960555708580000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 169865931623968716596460000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 158906839261132025203140000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 133138162624191696791820000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 120149073587685189787740000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 114560744583606808867380000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 104810893980746654921220000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 92945509756511184552780000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 83493424018560894598260000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (101 : ZMod 4926112017095092781297340001) ^ 80755934706476930840940000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_7389168025642639171946010001 : Nat.Prime 7389168025642639171946010001 := by
  apply lucas_primality 7389168025642639171946010001 (73 : ZMod 7389168025642639171946010001)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 7389168025642639171946010001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_5
      · exact prime_fiftyAV_7
      · exact prime_fiftyAV_11
      · exact prime_fiftyAV_13
      · exact prime_fiftyAV_17
      · exact prime_fiftyAV_19
      · exact prime_fiftyAV_23
      · exact prime_fiftyAV_29
      · exact prime_fiftyAV_31
      · exact prime_fiftyAV_37
      · exact prime_fiftyAV_41
      · exact prime_fiftyAV_43
      · exact prime_fiftyAV_47
      · exact prime_fiftyAV_53
      · exact prime_fiftyAV_59
      · exact prime_fiftyAV_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 7389168025642639171946010001) ^ 3694584012821319585973005000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 2463056008547546390648670000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 1477833605128527834389202000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 1055595432234662738849430000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 671742547785694470176910000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 568397540434049167072770000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 434656942684861127761530000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 388903580296981009049790000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 321268175027940833562870000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 254798897435953074894690000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 238360258891698037804710000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 199707243936287545187730000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 180223610381527784681610000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 171841116875410213301070000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 157216340971119982381830000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 139418264634766776829170000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 125240136027841341897390000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (73 : ZMod 7389168025642639171946010001) ^ 121133902059715396261410000 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem prime_fiftyAV_59113344205141113375568080073 : Nat.Prime 59113344205141113375568080073 := by
  apply lucas_primality 59113344205141113375568080073 (7 : ZMod 59113344205141113375568080073)
  · rw [← fiftyAVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4999, 1), (6793, 1), (20983, 1), (1152234038950921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4999, 1), (6793, 1), (20983, 1), (1152234038950921, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyAV_2
      · exact prime_fiftyAV_3
      · exact prime_fiftyAV_4999
      · exact prime_fiftyAV_6793
      · exact prime_fiftyAV_20983
      · exact prime_fiftyAV_1152234038950921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 59113344205141113375568080073) ^ 29556672102570556687784040036 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 59113344205141113375568080073) ^ 19704448068380371125189360024 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 59113344205141113375568080073) ^ 11825033847797782231559928 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 59113344205141113375568080073) ^ 8702096894618153006855304 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 59113344205141113375568080073) ^ 2817201744514183547422584 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide
    · change (7 : ZMod 59113344205141113375568080073) ^ 51303244138632 ≠ 1
      rw [← fiftyAVFastPow_eq_pow]
      decide

private theorem phi_fiftyAV_59113344205141113375568080000 : Nat.totient 59113344205141113375568080000 = 7778568422968031969280000000 := by
  rw [← show ((([(2, 7), (3, 3), (5, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_5, prime_fiftyAV_7, prime_fiftyAV_11, prime_fiftyAV_13, prime_fiftyAV_17, prime_fiftyAV_19, prime_fiftyAV_23, prime_fiftyAV_29, prime_fiftyAV_31, prime_fiftyAV_37, prime_fiftyAV_41, prime_fiftyAV_43, prime_fiftyAV_47, prime_fiftyAV_53, prime_fiftyAV_59, prime_fiftyAV_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080001 : Nat.totient 59113344205141113375568080001 = 59025258206037971472533219584 := by
  rw [← show ((([(677, 1), (90353, 1), (508367, 1), (1900977306686963, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_677, prime_fiftyAV_90353, prime_fiftyAV_508367, prime_fiftyAV_1900977306686963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080002 : Nat.totient 59113344205141113375568080002 = 29403528723263640873416573952 := by
  rw [← show ((([(2, 1), (193, 1), (54743994013, 1), (2797446213614389, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_193, prime_fiftyAV_54743994013, prime_fiftyAV_2797446213614389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080003 : Nat.totient 59113344205141113375568080003 = 39338144079064582928564753504 := by
  rw [← show ((([(3, 1), (557, 1), (35376028848079660906982693, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_557, prime_fiftyAV_35376028848079660906982693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080004 : Nat.totient 59113344205141113375568080004 = 29406638234029589394952648544 := by
  rw [← show ((([(2, 2), (197, 1), (75016934270483646415695533, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_197, prime_fiftyAV_75016934270483646415695533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080005 : Nat.totient 59113344205141113375568080005 = 47211968900363400164906352192 := by
  rw [← show ((([(5, 1), (859, 1), (1997, 1), (6891984566505300835487, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_5, prime_fiftyAV_859, prime_fiftyAV_1997, prime_fiftyAV_6891984566505300835487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080006 : Nat.totient 59113344205141113375568080006 = 19661889818662073510184111840 := by
  rw [← show ((([(2, 1), (3, 1), (463, 1), (422410757, 1), (50375378072400611, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_463, prime_fiftyAV_422410757, prime_fiftyAV_50375378072400611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080007 : Nat.totient 59113344205141113375568080007 = 50668580747255213571942566400 := by
  rw [← show ((([(7, 1), (5917576318961, 1), (1427064562026641, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_7, prime_fiftyAV_5917576318961, prime_fiftyAV_1427064562026641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080008 : Nat.totient 59113344205141113375568080008 = 29556672102570556687784040000 := by
  rw [← show ((([(2, 3), (7389168025642639171946010001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_7389168025642639171946010001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080009 : Nat.totient 59113344205141113375568080009 = 38934040514366652518969763840 := by
  rw [← show ((([(3, 2), (107, 1), (373, 1), (22481, 1), (259949, 1), (28160906695139, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_107, prime_fiftyAV_373, prime_fiftyAV_22481, prime_fiftyAV_259949, prime_fiftyAV_28160906695139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080010 : Nat.totient 59113344205141113375568080010 = 23645173098297522210896442048 := by
  rw [← show ((([(2, 1), (5, 1), (143669, 1), (13852339783, 1), (2970293224763, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_5, prime_fiftyAV_143669, prime_fiftyAV_13852339783, prime_fiftyAV_2970293224763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080011 : Nat.totient 59113344205141113375568080011 = 53246381769434864425032131040 := by
  rw [← show ((([(11, 1), (109, 1), (49302205342069318912066789, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_11, prime_fiftyAV_109, prime_fiftyAV_49302205342069318912066789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080012 : Nat.totient 59113344205141113375568080012 = 19704448068380371125189360000 := by
  rw [← show ((([(2, 2), (3, 1), (4926112017095092781297340001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_4926112017095092781297340001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080013 : Nat.totient 59113344205141113375568080013 = 54563824696866487916550736944 := by
  rw [← show ((([(13, 1), (23327, 1), (194932066852676869575263, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_13, prime_fiftyAV_23327, prime_fiftyAV_194932066852676869575263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080014 : Nat.totient 59113344205141113375568080014 = 25333735976066079057575439360 := by
  rw [← show ((([(2, 1), (7, 1), (45697, 1), (81709378843, 1), (1130831493331, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_7, prime_fiftyAV_45697, prime_fiftyAV_81709378843, prime_fiftyAV_1130831493331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080015 : Nat.totient 59113344205141113375568080015 = 31527031606949144126158848000 := by
  rw [← show ((([(3, 1), (5, 1), (374681, 1), (27212041, 1), (386519565736481, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_5, prime_fiftyAV_374681, prime_fiftyAV_27212041, prime_fiftyAV_386519565736481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080016 : Nat.totient 59113344205141113375568080016 = 29250812797412873202424627200 := by
  rw [← show ((([(2, 4), (97, 1), (25411, 1), (152559443, 1), (9825009110321, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_97, prime_fiftyAV_25411, prime_fiftyAV_152559443, prime_fiftyAV_9825009110321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080017 : Nat.totient 59113344205141113375568080017 = 55493063534926989541386563328 := by
  rw [← show ((([(17, 1), (389, 1), (31448647, 1), (284239899442134347, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_17, prime_fiftyAV_389, prime_fiftyAV_31448647, prime_fiftyAV_284239899442134347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080018 : Nat.totient 59113344205141113375568080018 = 19600920102401723089442880000 := by
  rw [← show ((([(2, 1), (3, 2), (191, 1), (53951, 1), (318698601733276800961, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_191, prime_fiftyAV_53951, prime_fiftyAV_318698601733276800961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080019 : Nat.totient 59113344205141113375568080019 = 56002082255195417051345418528 := by
  rw [← show ((([(19, 2), (1681363, 1), (97390555111845758233, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_19, prime_fiftyAV_1681363, prime_fiftyAV_97390555111845758233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080020 : Nat.totient 59113344205141113375568080020 = 23534468606329811678520594432 := by
  rw [← show ((([(2, 2), (5, 1), (223, 1), (5113, 1), (101287, 1), (25592998416424177, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_5, prime_fiftyAV_223, prime_fiftyAV_5113, prime_fiftyAV_101287, prime_fiftyAV_25592998416424177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080021 : Nat.totient 59113344205141113375568080021 = 33703822085782015643976450048 := by
  rw [← show ((([(3, 1), (7, 1), (449, 1), (6269312143932666600442049, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_7, prime_fiftyAV_449, prime_fiftyAV_6269312143932666600442049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080022 : Nat.totient 59113344205141113375568080022 = 26869701911427778807076400000 := by
  rw [← show ((([(2, 1), (11, 1), (2686970191142777880707640001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_11, prime_fiftyAV_2686970191142777880707640001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080023 : Nat.totient 59113344205141113375568080023 = 55907866767732058320887796480 := by
  rw [← show ((([(23, 1), (89, 1), (3843031, 1), (86253907, 1), (87119429477, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_23, prime_fiftyAV_89, prime_fiftyAV_3843031, prime_fiftyAV_86253907, prime_fiftyAV_87119429477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080024 : Nat.totient 59113344205141113375568080024 = 19164325167756734552674813440 := by
  rw [← show ((([(2, 3), (3, 1), (67, 1), (79, 1), (58789, 1), (2049369011, 1), (3862390283, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_67, prime_fiftyAV_79, prime_fiftyAV_58789, prime_fiftyAV_2049369011, prime_fiftyAV_3862390283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080025 : Nat.totient 59113344205141113375568080025 = 47290450377194372420152151040 := by
  rw [← show ((([(5, 2), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_5, prime_fiftyAV_210193, prime_fiftyAV_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080026 : Nat.totient 59113344205141113375568080026 = 27283038301797923885774400048 := by
  rw [← show ((([(2, 1), (13, 1), (625199, 1), (3636586369677809254799, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_13, prime_fiftyAV_625199, prime_fiftyAV_3636586369677809254799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080027 : Nat.totient 59113344205141113375568080027 = 39408896136760742250378719964 := by
  rw [← show ((([(3, 4), (729794372902976708340346667, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_729794372902976708340346667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080028 : Nat.totient 59113344205141113375568080028 = 25132302223194052451380838400 := by
  rw [← show ((([(2, 2), (7, 1), (149, 1), (997, 1), (4259, 1), (36013, 1), (211441, 1), (438217711, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_7, prime_fiftyAV_149, prime_fiftyAV_997, prime_fiftyAV_4259, prime_fiftyAV_36013, prime_fiftyAV_211441, prime_fiftyAV_438217711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080029 : Nat.totient 59113344205141113375568080029 = 57071810620713016633802256960 := by
  rw [← show ((([(29, 1), (18223, 1), (5500067, 1), (20337598823458661, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_29, prime_fiftyAV_18223, prime_fiftyAV_5500067, prime_fiftyAV_20337598823458661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080030 : Nat.totient 59113344205141113375568080030 = 15547617939473564325614668800 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (73, 1), (13737811, 1), (68784581, 1), (28564904807, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_5, prime_fiftyAV_73, prime_fiftyAV_13737811, prime_fiftyAV_68784581, prime_fiftyAV_28564904807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080031 : Nat.totient 59113344205141113375568080031 = 57077327904297185457798321600 := by
  rw [← show ((([(31, 1), (443, 1), (15535459337, 1), (277074150678811, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_31, prime_fiftyAV_443, prime_fiftyAV_15535459337, prime_fiftyAV_277074150678811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080032 : Nat.totient 59113344205141113375568080032 = 29555740919806857668953382400 := by
  rw [← show ((([(2, 5), (31741, 1), (58198922731188676884361, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_31741, prime_fiftyAV_58198922731188676884361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080033 : Nat.totient 59113344205141113375568080033 = 35826269215237038409435200000 := by
  rw [← show ((([(3, 1), (11, 1), (1791313460761851920471760001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_11, prime_fiftyAV_1791313460761851920471760001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080034 : Nat.totient 59113344205141113375568080034 = 27647381483169571611236457792 := by
  rw [← show ((([(2, 1), (17, 1), (163, 1), (10666428041346285343841227, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_17, prime_fiftyAV_163, prime_fiftyAV_10666428041346285343841227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080035 : Nat.totient 59113344205141113375568080035 = 40474634441472175955375877120 := by
  rw [← show ((([(5, 1), (7, 1), (673, 1), (889647091, 1), (2820880298726107, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_5, prime_fiftyAV_7, prime_fiftyAV_673, prime_fiftyAV_889647091, prime_fiftyAV_2820880298726107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080036 : Nat.totient 59113344205141113375568080036 = 19704448068380371125189360000 := by
  rw [← show ((([(2, 2), (3, 2), (1642037339031697593765780001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_1642037339031697593765780001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080037 : Nat.totient 59113344205141113375568080037 = 57286532957047178105115720000 := by
  rw [← show ((([(37, 2), (251, 1), (8027563, 1), (21430121685966821, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_37, prime_fiftyAV_251, prime_fiftyAV_8027563, prime_fiftyAV_21430121685966821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080038 : Nat.totient 59113344205141113375568080038 = 27996095614335952797785145600 := by
  rw [← show ((([(2, 1), (19, 1), (6871, 1), (32491, 1), (1109609, 1), (6279845155949, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_19, prime_fiftyAV_6871, prime_fiftyAV_32491, prime_fiftyAV_1109609, prime_fiftyAV_6279845155949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080039 : Nat.totient 59113344205141113375568080039 = 35863493567014500684661203840 := by
  rw [← show ((([(3, 1), (13, 1), (71, 1), (23167, 1), (842587, 1), (1093649152175339, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_13, prime_fiftyAV_71, prime_fiftyAV_23167, prime_fiftyAV_842587, prime_fiftyAV_1093649152175339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080040 : Nat.totient 59113344205141113375568080040 = 23645337682056445350227232000 := by
  rw [← show ((([(2, 3), (5, 1), (1477833605128527834389202001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_5, prime_fiftyAV_1477833605128527834389202001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080041 : Nat.totient 59113344205141113375568080041 = 57250594953251906114335392000 := by
  rw [← show ((([(41, 1), (137, 1), (515717623, 1), (20406528643363151, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_41, prime_fiftyAV_137, prime_fiftyAV_515717623, prime_fiftyAV_20406528643363151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080042 : Nat.totient 59113344205141113375568080042 = 16817888982118899855498624000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (269, 1), (1901, 1), (248528221, 1), (11074551087949, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_7, prime_fiftyAV_269, prime_fiftyAV_1901, prime_fiftyAV_248528221, prime_fiftyAV_11074551087949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080043 : Nat.totient 59113344205141113375568080043 = 57738473462244313054798574400 := by
  rw [← show ((([(43, 1), (583351, 1), (1348073, 1), (1748129962376687, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_43, prime_fiftyAV_583351, prime_fiftyAV_1348073, prime_fiftyAV_1748129962376687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080044 : Nat.totient 59113344205141113375568080044 = 26862827926131842038649280000 := by
  rw [← show ((([(2, 2), (11, 1), (3911, 1), (7268321, 1), (47261873941684471, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_11, prime_fiftyAV_3911, prime_fiftyAV_7268321, prime_fiftyAV_47261873941684471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080045 : Nat.totient 59113344205141113375568080045 = 31527116909276032718934423648 := by
  rw [← show ((([(3, 2), (5, 1), (237841108607, 1), (5523140549247743, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_5, prime_fiftyAV_237841108607, prime_fiftyAV_5523140549247743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080046 : Nat.totient 59113344205141113375568080046 = 27961068808588633476433145856 := by
  rw [← show ((([(2, 1), (23, 1), (167, 1), (199, 1), (1273889, 1), (30354743159973073, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_23, prime_fiftyAV_167, prime_fiftyAV_199, prime_fiftyAV_1273889, prime_fiftyAV_30354743159973073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080047 : Nat.totient 59113344205141113375568080047 = 57646748446767921915370779552 := by
  rw [← show ((([(47, 1), (277, 1), (4540544143570252198753213, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_47, prime_fiftyAV_277, prime_fiftyAV_4540544143570252198753213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080048 : Nat.totient 59113344205141113375568080048 = 19704440480667508395793137664 := by
  rw [← show ((([(2, 4), (3, 1), (2596889, 1), (474232053920584667009, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_2596889, prime_fiftyAV_474232053920584667009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080049 : Nat.totient 59113344205141113375568080049 = 50666315419739008683376575144 := by
  rw [← show ((([(7, 2), (22367, 1), (53936369638161461788703, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_7, prime_fiftyAV_22367, prime_fiftyAV_53936369638161461788703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080050 : Nat.totient 59113344205141113375568080050 = 23411096557065912790019523840 := by
  rw [← show ((([(2, 1), (5, 2), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_5, prime_fiftyAV_103, prime_fiftyAV_5009, prime_fiftyAV_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080051 : Nat.totient 59113344205141113375568080051 = 37065681396452888608212531200 := by
  rw [← show ((([(3, 1), (17, 1), (1481, 1), (782636853810238357436921, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_17, prime_fiftyAV_1481, prime_fiftyAV_782636853810238357436921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080052 : Nat.totient 59113344205141113375568080052 = 27280523237509667846329120512 := by
  rw [← show ((([(2, 2), (13, 1), (10687, 1), (4719079, 1), (22540789770483337, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_13, prime_fiftyAV_10687, prime_fiftyAV_4719079, prime_fiftyAV_22540789770483337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080053 : Nat.totient 59113344205141113375568080053 = 57942299467833300585799269120 := by
  rw [← show ((([(53, 1), (1621, 1), (3019, 1), (80687, 1), (45503099, 1), (62075323, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_53, prime_fiftyAV_1621, prime_fiftyAV_3019, prime_fiftyAV_80687, prime_fiftyAV_45503099, prime_fiftyAV_62075323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080054 : Nat.totient 59113344205141113375568080054 = 19703084155590976761575533896 := by
  rw [← show ((([(2, 1), (3, 3), (14447, 1), (75772932744131311864783, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_14447, prime_fiftyAV_75772932744131311864783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080055 : Nat.totient 59113344205141113375568080055 = 42991523058284446091322240000 := by
  rw [← show ((([(5, 1), (11, 1), (1074788076457111152283056001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_5, prime_fiftyAV_11, prime_fiftyAV_1074788076457111152283056001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080056 : Nat.totient 59113344205141113375568080056 = 25334290373624836861157062368 := by
  rw [← show ((([(2, 3), (7, 1), (3628626968867, 1), (290907674250203, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_7, prime_fiftyAV_3628626968867, prime_fiftyAV_290907674250203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080057 : Nat.totient 59113344205141113375568080057 = 37148930157142159073822797056 := by
  rw [← show ((([(3, 1), (19, 1), (317, 1), (547, 1), (58376880557, 1), (102452651107, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_19, prime_fiftyAV_317, prime_fiftyAV_547, prime_fiftyAV_58376880557, prime_fiftyAV_102452651107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080058 : Nat.totient 59113344205141113375568080058 = 28537475065004050703441666496 := by
  rw [← show ((([(2, 1), (29, 1), (21268679, 1), (269471693, 1), (177829524883, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_29, prime_fiftyAV_21268679, prime_fiftyAV_269471693, prime_fiftyAV_177829524883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080059 : Nat.totient 59113344205141113375568080059 = 58111268173290840176259085440 := by
  rw [← show ((([(59, 1), (375121, 1), (1951638919, 1), (1368556305799, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_59, prime_fiftyAV_375121, prime_fiftyAV_1951638919, prime_fiftyAV_1368556305799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080060 : Nat.totient 59113344205141113375568080060 = 15682048430677405310133927936 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (283, 1), (613, 1), (85303, 1), (66576822500643073, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_5, prime_fiftyAV_283, prime_fiftyAV_613, prime_fiftyAV_85303, prime_fiftyAV_66576822500643073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080061 : Nat.totient 59113344205141113375568080061 = 58144272988663390205476800000 := by
  rw [← show ((([(61, 1), (969071216477723170091280001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_61, prime_fiftyAV_969071216477723170091280001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080062 : Nat.totient 59113344205141113375568080062 = 28583186756515324617478566360 := by
  rw [← show ((([(2, 1), (31, 1), (1427, 1), (668143682947997302886363, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_31, prime_fiftyAV_1427, prime_fiftyAV_668143682947997302886363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080063 : Nat.totient 59113344205141113375568080063 = 33779053831505671898274297600 := by
  rw [← show ((([(3, 2), (7, 1), (10724678746921, 1), (87490457571481, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_7, prime_fiftyAV_10724678746921, prime_fiftyAV_87490457571481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080064 : Nat.totient 59113344205141113375568080064 = 29528004137305573040801802240 := by
  rw [← show ((([(2, 6), (1031, 1), (428348173229, 1), (2091461964649, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_1031, prime_fiftyAV_428348173229, prime_fiftyAV_2091461964649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080065 : Nat.totient 59113344205141113375568080065 = 43652931105334976031188736000 := by
  rw [← show ((([(5, 1), (13, 1), (909436064694478667316432001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_5, prime_fiftyAV_13, prime_fiftyAV_909436064694478667316432001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080066 : Nat.totient 59113344205141113375568080066 = 17912756938720319253071683200 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (47431, 1), (10834859807, 1), (1742833970153, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_11, prime_fiftyAV_47431, prime_fiftyAV_10834859807, prime_fiftyAV_1742833970153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080067 : Nat.totient 59113344205141113375568080067 = 58659408383363348787992712960 := by
  rw [← show ((([(131, 1), (21817, 1), (621772253, 1), (33265025793757, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_131, prime_fiftyAV_21817, prime_fiftyAV_621772253, prime_fiftyAV_33265025793757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080068 : Nat.totient 59113344205141113375568080068 = 27776444915858422984084684800 := by
  rw [← show ((([(2, 2), (17, 1), (937, 1), (2333, 1), (6786591521, 1), (58596351661, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_17, prime_fiftyAV_937, prime_fiftyAV_2333, prime_fiftyAV_6786591521, prime_fiftyAV_58596351661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080069 : Nat.totient 59113344205141113375568080069 = 37591601670217079449298212032 := by
  rw [← show ((([(3, 1), (23, 1), (419, 1), (2707, 1), (5416363, 1), (139452529777019, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_23, prime_fiftyAV_419, prime_fiftyAV_2707, prime_fiftyAV_5416363, prime_fiftyAV_139452529777019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080070 : Nat.totient 59113344205141113375568080070 = 20087705161651515460698931200 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (113, 1), (54421, 1), (97654321, 1), (1406212853597, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_5, prime_fiftyAV_7, prime_fiftyAV_113, prime_fiftyAV_54421, prime_fiftyAV_97654321, prime_fiftyAV_1406212853597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080071 : Nat.totient 59113344205141113375568080071 = 58688068347550170113873345544 := by
  rw [← show ((([(139, 1), (425275857590943261694734389, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_139, prime_fiftyAV_425275857590943261694734389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080072 : Nat.totient 59113344205141113375568080072 = 19696667530537685413124904960 := by
  rw [← show ((([(2, 3), (3, 2), (4999, 1), (6793, 1), (20983, 1), (1152234038950921, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_4999, prime_fiftyAV_6793, prime_fiftyAV_20983, prime_fiftyAV_1152234038950921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080073 : Nat.totient 59113344205141113375568080073 = 59113344205141113375568080072 := by
  rw [← show ((([(59113344205141113375568080073, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_59113344205141113375568080073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080074 : Nat.totient 59113344205141113375568080074 = 28751715492870691879150739328 := by
  rw [← show ((([(2, 1), (37, 1), (7559, 1), (12377, 1), (8538352360051590607, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_37, prime_fiftyAV_7559, prime_fiftyAV_12377, prime_fiftyAV_8538352360051590607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080075 : Nat.totient 59113344205141113375568080075 = 31430994585217978242885120000 := by
  rw [← show ((([(3, 1), (5, 2), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_5, prime_fiftyAV_421, prime_fiftyAV_1483, prime_fiftyAV_2072201, prime_fiftyAV_2567179, prime_fiftyAV_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080076 : Nat.totient 59113344205141113375568080076 = 28001057781363236592947085312 := by
  rw [← show ((([(2, 2), (19, 1), (1447535876737, 1), (537331870728673, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_19, prime_fiftyAV_1447535876737, prime_fiftyAV_537331870728673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080077 : Nat.totient 59113344205141113375568080077 = 45699649547766686347587022080 := by
  rw [← show ((([(7, 1), (11, 2), (127, 1), (48244037, 1), (11390813889425209, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_7, prime_fiftyAV_11, prime_fiftyAV_127, prime_fiftyAV_48244037, prime_fiftyAV_11390813889425209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080078 : Nat.totient 59113344205141113375568080078 = 18188721293889573346328640000 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (757863387245398889430360001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_13, prime_fiftyAV_757863387245398889430360001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080079 : Nat.totient 59113344205141113375568080079 = 59113344204626006293908870400 := by
  rw [← show ((([(114759356801, 1), (515106966899852879, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_114759356801, prime_fiftyAV_515106966899852879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080080 : Nat.totient 59113344205141113375568080080 = 23360437581727748616583884800 := by
  rw [← show ((([(2, 4), (5, 1), (83, 1), (1433741, 1), (106163831, 1), (58488456857, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_5, prime_fiftyAV_83, prime_fiftyAV_1433741, prime_fiftyAV_106163831, prime_fiftyAV_58488456857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080081 : Nat.totient 59113344205141113375568080081 = 39337335314283841722834091200 := by
  rw [← show ((([(3, 3), (571, 1), (15467, 1), (2061564319, 1), (120249334741, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_571, prime_fiftyAV_15467, prime_fiftyAV_2061564319, prime_fiftyAV_120249334741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080082 : Nat.totient 59113344205141113375568080082 = 28835576976378045356650667680 := by
  rw [← show ((([(2, 1), (41, 1), (143687, 1), (5017116660004810029623, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_41, prime_fiftyAV_143687, prime_fiftyAV_5017116660004810029623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080083 : Nat.totient 59113344205141113375568080083 = 59113289740048002935141702400 := by
  rw [← show ((([(1120081, 1), (34996123, 1), (1508051471281241, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_1120081, prime_fiftyAV_34996123, prime_fiftyAV_1508051471281241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080084 : Nat.totient 59113344205141113375568080084 = 16889516328030026587243009920 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (1791037, 1), (14588891, 1), (26932669760303, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_7, prime_fiftyAV_1791037, prime_fiftyAV_14588891, prime_fiftyAV_26932669760303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080085 : Nat.totient 59113344205141113375568080085 = 44508870929100445614962150400 := by
  rw [← show ((([(5, 1), (17, 1), (24330664621, 1), (28583317353999781, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_5, prime_fiftyAV_17, prime_fiftyAV_24330664621, prime_fiftyAV_28583317353999781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080086 : Nat.totient 59113344205141113375568080086 = 28594294780977697219505971200 := by
  rw [← show ((([(2, 1), (43, 1), (179, 1), (271, 1), (3677, 1), (1467937, 1), (2625207939961, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_43, prime_fiftyAV_179, prime_fiftyAV_271, prime_fiftyAV_3677, prime_fiftyAV_1467937, prime_fiftyAV_2625207939961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080087 : Nat.totient 59113344205141113375568080087 = 38048922394009973821105151232 := by
  rw [← show ((([(3, 1), (29, 1), (36383, 1), (80523799, 1), (231922836591353, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_29, prime_fiftyAV_36383, prime_fiftyAV_80523799, prime_fiftyAV_231922836591353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080088 : Nat.totient 59113344205141113375568080088 = 26869700255920747109999226880 := by
  rw [← show ((([(2, 3), (11, 1), (16230497, 1), (41387675792410698833, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_11, prime_fiftyAV_16230497, prime_fiftyAV_41387675792410698833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080089 : Nat.totient 59113344205141113375568080089 = 59102043612810800614030119600 := by
  rw [← show ((([(5231, 1), (5696273509, 1), (1983855223395691, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_5231, prime_fiftyAV_5696273509, prime_fiftyAV_1983855223395691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080090 : Nat.totient 59113344205141113375568080090 = 15735419455154738074399153152 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (569, 1), (37039, 1), (1544987, 1), (20171893710853, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_5, prime_fiftyAV_569, prime_fiftyAV_37039, prime_fiftyAV_1544987, prime_fiftyAV_20171893710853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080091 : Nat.totient 59113344205141113375568080091 = 46006247300896266229689212160 := by
  rw [← show ((([(7, 1), (13, 1), (67, 1), (691, 1), (14031086011350298342633, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_7, prime_fiftyAV_13, prime_fiftyAV_67, prime_fiftyAV_691, prime_fiftyAV_14031086011350298342633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080092 : Nat.totient 59113344205141113375568080092 = 28263246141154839904116403200 := by
  rw [← show ((([(2, 2), (23, 1), (5779, 1), (8167, 1), (624578257, 1), (21796943101, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_23, prime_fiftyAV_5779, prime_fiftyAV_8167, prime_fiftyAV_624578257, prime_fiftyAV_21796943101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080093 : Nat.totient 59113344205141113375568080093 = 38137641422671686048753600000 := by
  rw [← show ((([(3, 1), (31, 1), (635627357044528100812560001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_31, prime_fiftyAV_635627357044528100812560001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080094 : Nat.totient 59113344205141113375568080094 = 28927806738686076758256720000 := by
  rw [← show ((([(2, 1), (47, 1), (628865363884479929527320001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_47, prime_fiftyAV_628865363884479929527320001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080095 : Nat.totient 59113344205141113375568080095 = 44801673737091684638262266880 := by
  rw [← show ((([(5, 1), (19, 1), (2428859, 1), (167470561, 1), (1529752406099, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_5, prime_fiftyAV_19, prime_fiftyAV_2428859, prime_fiftyAV_167470561, prime_fiftyAV_1529752406099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080096 : Nat.totient 59113344205141113375568080096 = 19501222086195696149344870400 := by
  rw [← show ((([(2, 5), (3, 1), (101, 1), (2399, 1), (129334193, 1), (19649401054343, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_3, prime_fiftyAV_101, prime_fiftyAV_2399, prime_fiftyAV_129334193, prime_fiftyAV_19649401054343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080097 : Nat.totient 59113344205141113375568080097 = 58833185061394674559766088000 := by
  rw [← show ((([(211, 1), (57732893, 1), (675548051, 1), (7183291789, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_211, prime_fiftyAV_57732893, prime_fiftyAV_675548051, prime_fiftyAV_7183291789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080098 : Nat.totient 59113344205141113375568080098 = 25334290361408205926755031424 := by
  rw [← show ((([(2, 1), (7, 2), (2072555033, 1), (291040469490094697, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_7, prime_fiftyAV_2072555033, prime_fiftyAV_291040469490094697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080099 : Nat.totient 59113344205141113375568080099 = 35817182463070403370815353920 := by
  rw [← show ((([(3, 2), (11, 1), (3943, 1), (50536133, 1), (2996550152403179, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_3, prime_fiftyAV_11, prime_fiftyAV_3943, prime_fiftyAV_50536133, prime_fiftyAV_2996550152403179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyAV_59113344205141113375568080100 : Nat.totient 59113344205141113375568080100 = 23645337662716489815288244000 := by
  rw [← show ((([(2, 2), (5, 2), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 59113344205141113375568080100 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyAV_2, prime_fiftyAV_5, prime_fiftyAV_1222615931, prime_fiftyAV_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftyAV : certifiedKill 1 59113344205141113375568079999 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftyAV_59113344205141113375568080000, phi_fiftyAV_59113344205141113375568080001, phi_fiftyAV_59113344205141113375568080002,
    phi_fiftyAV_59113344205141113375568080003, phi_fiftyAV_59113344205141113375568080004, phi_fiftyAV_59113344205141113375568080005,
    phi_fiftyAV_59113344205141113375568080006, phi_fiftyAV_59113344205141113375568080007, phi_fiftyAV_59113344205141113375568080008,
    phi_fiftyAV_59113344205141113375568080009, phi_fiftyAV_59113344205141113375568080010, phi_fiftyAV_59113344205141113375568080011,
    phi_fiftyAV_59113344205141113375568080012, phi_fiftyAV_59113344205141113375568080013, phi_fiftyAV_59113344205141113375568080014,
    phi_fiftyAV_59113344205141113375568080015, phi_fiftyAV_59113344205141113375568080016, phi_fiftyAV_59113344205141113375568080017,
    phi_fiftyAV_59113344205141113375568080018, phi_fiftyAV_59113344205141113375568080019, phi_fiftyAV_59113344205141113375568080020,
    phi_fiftyAV_59113344205141113375568080021, phi_fiftyAV_59113344205141113375568080022, phi_fiftyAV_59113344205141113375568080023,
    phi_fiftyAV_59113344205141113375568080024, phi_fiftyAV_59113344205141113375568080025, phi_fiftyAV_59113344205141113375568080026,
    phi_fiftyAV_59113344205141113375568080027, phi_fiftyAV_59113344205141113375568080028, phi_fiftyAV_59113344205141113375568080029,
    phi_fiftyAV_59113344205141113375568080030, phi_fiftyAV_59113344205141113375568080031, phi_fiftyAV_59113344205141113375568080032,
    phi_fiftyAV_59113344205141113375568080033, phi_fiftyAV_59113344205141113375568080034, phi_fiftyAV_59113344205141113375568080035,
    phi_fiftyAV_59113344205141113375568080036, phi_fiftyAV_59113344205141113375568080037, phi_fiftyAV_59113344205141113375568080038,
    phi_fiftyAV_59113344205141113375568080039, phi_fiftyAV_59113344205141113375568080040, phi_fiftyAV_59113344205141113375568080041,
    phi_fiftyAV_59113344205141113375568080042, phi_fiftyAV_59113344205141113375568080043, phi_fiftyAV_59113344205141113375568080044,
    phi_fiftyAV_59113344205141113375568080045, phi_fiftyAV_59113344205141113375568080046, phi_fiftyAV_59113344205141113375568080047,
    phi_fiftyAV_59113344205141113375568080048, phi_fiftyAV_59113344205141113375568080049, phi_fiftyAV_59113344205141113375568080050,
    phi_fiftyAV_59113344205141113375568080051, phi_fiftyAV_59113344205141113375568080052, phi_fiftyAV_59113344205141113375568080053,
    phi_fiftyAV_59113344205141113375568080054, phi_fiftyAV_59113344205141113375568080055, phi_fiftyAV_59113344205141113375568080056,
    phi_fiftyAV_59113344205141113375568080057, phi_fiftyAV_59113344205141113375568080058, phi_fiftyAV_59113344205141113375568080059,
    phi_fiftyAV_59113344205141113375568080060, phi_fiftyAV_59113344205141113375568080061, phi_fiftyAV_59113344205141113375568080062,
    phi_fiftyAV_59113344205141113375568080063, phi_fiftyAV_59113344205141113375568080064, phi_fiftyAV_59113344205141113375568080065,
    phi_fiftyAV_59113344205141113375568080066, phi_fiftyAV_59113344205141113375568080067, phi_fiftyAV_59113344205141113375568080068,
    phi_fiftyAV_59113344205141113375568080069, phi_fiftyAV_59113344205141113375568080070, phi_fiftyAV_59113344205141113375568080071,
    phi_fiftyAV_59113344205141113375568080072, phi_fiftyAV_59113344205141113375568080073, phi_fiftyAV_59113344205141113375568080074,
    phi_fiftyAV_59113344205141113375568080075, phi_fiftyAV_59113344205141113375568080076, phi_fiftyAV_59113344205141113375568080077,
    phi_fiftyAV_59113344205141113375568080078, phi_fiftyAV_59113344205141113375568080079, phi_fiftyAV_59113344205141113375568080080,
    phi_fiftyAV_59113344205141113375568080081, phi_fiftyAV_59113344205141113375568080082, phi_fiftyAV_59113344205141113375568080083,
    phi_fiftyAV_59113344205141113375568080084, phi_fiftyAV_59113344205141113375568080085, phi_fiftyAV_59113344205141113375568080086,
    phi_fiftyAV_59113344205141113375568080087, phi_fiftyAV_59113344205141113375568080088, phi_fiftyAV_59113344205141113375568080089,
    phi_fiftyAV_59113344205141113375568080090, phi_fiftyAV_59113344205141113375568080091, phi_fiftyAV_59113344205141113375568080092,
    phi_fiftyAV_59113344205141113375568080093, phi_fiftyAV_59113344205141113375568080094, phi_fiftyAV_59113344205141113375568080095,
    phi_fiftyAV_59113344205141113375568080096, phi_fiftyAV_59113344205141113375568080097, phi_fiftyAV_59113344205141113375568080098,
    phi_fiftyAV_59113344205141113375568080099, phi_fiftyAV_59113344205141113375568080100]

end TotientTailPeriodKiller
end Erdos249257
