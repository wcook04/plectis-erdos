import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirteenKFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirteenKFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirteenKFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirteenKFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirteenKFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirteenKFastPow a n * thirteenKFastPow a n * a
        else thirteenKFastPow a n * thirteenKFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirteenK_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirteenK_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirteenK_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirteenK_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirteenK_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirteenK_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirteenK_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirteenK_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirteenK_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirteenK_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirteenK_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirteenK_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirteenK_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirteenK_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirteenK_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirteenK_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirteenK_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirteenK_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirteenK_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirteenK_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirteenK_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirteenK_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirteenK_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirteenK_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirteenK_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirteenK_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirteenK_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirteenK_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirteenK_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirteenK_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirteenK_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirteenK_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirteenK_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirteenK_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirteenK_151 : Nat.Prime 151 := by norm_num
private theorem prime_thirteenK_157 : Nat.Prime 157 := by norm_num
private theorem prime_thirteenK_163 : Nat.Prime 163 := by norm_num
private theorem prime_thirteenK_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirteenK_173 : Nat.Prime 173 := by norm_num
private theorem prime_thirteenK_179 : Nat.Prime 179 := by norm_num
private theorem prime_thirteenK_181 : Nat.Prime 181 := by norm_num
private theorem prime_thirteenK_193 : Nat.Prime 193 := by norm_num
private theorem prime_thirteenK_199 : Nat.Prime 199 := by norm_num
private theorem prime_thirteenK_211 : Nat.Prime 211 := by norm_num
private theorem prime_thirteenK_227 : Nat.Prime 227 := by norm_num
private theorem prime_thirteenK_229 : Nat.Prime 229 := by norm_num
private theorem prime_thirteenK_233 : Nat.Prime 233 := by norm_num
private theorem prime_thirteenK_239 : Nat.Prime 239 := by norm_num
private theorem prime_thirteenK_251 : Nat.Prime 251 := by norm_num
private theorem prime_thirteenK_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirteenK_269 : Nat.Prime 269 := by norm_num
private theorem prime_thirteenK_277 : Nat.Prime 277 := by norm_num
private theorem prime_thirteenK_293 : Nat.Prime 293 := by norm_num
private theorem prime_thirteenK_307 : Nat.Prime 307 := by norm_num
private theorem prime_thirteenK_311 : Nat.Prime 311 := by norm_num
private theorem prime_thirteenK_313 : Nat.Prime 313 := by norm_num
private theorem prime_thirteenK_331 : Nat.Prime 331 := by norm_num
private theorem prime_thirteenK_359 : Nat.Prime 359 := by norm_num
private theorem prime_thirteenK_367 : Nat.Prime 367 := by norm_num
private theorem prime_thirteenK_389 : Nat.Prime 389 := by norm_num
private theorem prime_thirteenK_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirteenK_401 : Nat.Prime 401 := by norm_num
private theorem prime_thirteenK_409 : Nat.Prime 409 := by norm_num
private theorem prime_thirteenK_419 : Nat.Prime 419 := by norm_num
private theorem prime_thirteenK_431 : Nat.Prime 431 := by norm_num
private theorem prime_thirteenK_457 : Nat.Prime 457 := by norm_num
private theorem prime_thirteenK_461 : Nat.Prime 461 := by norm_num
private theorem prime_thirteenK_487 : Nat.Prime 487 := by norm_num
private theorem prime_thirteenK_499 : Nat.Prime 499 := by norm_num
private theorem prime_thirteenK_521 : Nat.Prime 521 := by norm_num
private theorem prime_thirteenK_523 : Nat.Prime 523 := by norm_num
private theorem prime_thirteenK_547 : Nat.Prime 547 := by norm_num
private theorem prime_thirteenK_557 : Nat.Prime 557 := by norm_num
private theorem prime_thirteenK_587 : Nat.Prime 587 := by norm_num
private theorem prime_thirteenK_607 : Nat.Prime 607 := by norm_num
private theorem prime_thirteenK_613 : Nat.Prime 613 := by norm_num
private theorem prime_thirteenK_617 : Nat.Prime 617 := by norm_num
private theorem prime_thirteenK_619 : Nat.Prime 619 := by norm_num
private theorem prime_thirteenK_653 : Nat.Prime 653 := by norm_num
private theorem prime_thirteenK_661 : Nat.Prime 661 := by norm_num
private theorem prime_thirteenK_719 : Nat.Prime 719 := by norm_num
private theorem prime_thirteenK_733 : Nat.Prime 733 := by norm_num
private theorem prime_thirteenK_821 : Nat.Prime 821 := by norm_num
private theorem prime_thirteenK_877 : Nat.Prime 877 := by norm_num
private theorem prime_thirteenK_881 : Nat.Prime 881 := by norm_num
private theorem prime_thirteenK_907 : Nat.Prime 907 := by norm_num
private theorem prime_thirteenK_967 : Nat.Prime 967 := by norm_num
private theorem prime_thirteenK_977 : Nat.Prime 977 := by norm_num
private theorem prime_thirteenK_983 : Nat.Prime 983 := by norm_num
private theorem prime_thirteenK_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_thirteenK_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_thirteenK_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_thirteenK_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_thirteenK_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_thirteenK_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_thirteenK_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_thirteenK_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_thirteenK_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_thirteenK_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_thirteenK_1237 : Nat.Prime 1237 := by norm_num
private theorem prime_thirteenK_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_thirteenK_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_thirteenK_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_thirteenK_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_thirteenK_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_thirteenK_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_thirteenK_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_thirteenK_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_thirteenK_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_thirteenK_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_thirteenK_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_thirteenK_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_thirteenK_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_thirteenK_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_thirteenK_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_thirteenK_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_thirteenK_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_thirteenK_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_thirteenK_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_thirteenK_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_thirteenK_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_thirteenK_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_thirteenK_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_thirteenK_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_thirteenK_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirteenK_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_thirteenK_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_thirteenK_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_thirteenK_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_thirteenK_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_thirteenK_2689 : Nat.Prime 2689 := by norm_num
private theorem prime_thirteenK_2767 : Nat.Prime 2767 := by norm_num
private theorem prime_thirteenK_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_thirteenK_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_thirteenK_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_thirteenK_3041 : Nat.Prime 3041 := by norm_num
private theorem prime_thirteenK_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_thirteenK_3191 : Nat.Prime 3191 := by norm_num
private theorem prime_thirteenK_3203 : Nat.Prime 3203 := by norm_num
private theorem prime_thirteenK_3259 : Nat.Prime 3259 := by norm_num
private theorem prime_thirteenK_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_thirteenK_3299 : Nat.Prime 3299 := by norm_num
private theorem prime_thirteenK_3331 : Nat.Prime 3331 := by norm_num
private theorem prime_thirteenK_3391 : Nat.Prime 3391 := by norm_num
private theorem prime_thirteenK_3463 : Nat.Prime 3463 := by norm_num
private theorem prime_thirteenK_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_thirteenK_3877 : Nat.Prime 3877 := by norm_num
private theorem prime_thirteenK_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_thirteenK_4243 : Nat.Prime 4243 := by norm_num
private theorem prime_thirteenK_4357 : Nat.Prime 4357 := by norm_num
private theorem prime_thirteenK_4583 : Nat.Prime 4583 := by norm_num
private theorem prime_thirteenK_4889 : Nat.Prime 4889 := by norm_num
private theorem prime_thirteenK_4919 : Nat.Prime 4919 := by norm_num
private theorem prime_thirteenK_4987 : Nat.Prime 4987 := by norm_num
private theorem prime_thirteenK_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirteenK_5021 : Nat.Prime 5021 := by norm_num
private theorem prime_thirteenK_5119 : Nat.Prime 5119 := by norm_num
private theorem prime_thirteenK_5209 : Nat.Prime 5209 := by norm_num
private theorem prime_thirteenK_5569 : Nat.Prime 5569 := by norm_num
private theorem prime_thirteenK_5683 : Nat.Prime 5683 := by norm_num
private theorem prime_thirteenK_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_thirteenK_6203 : Nat.Prime 6203 := by norm_num
private theorem prime_thirteenK_6217 : Nat.Prime 6217 := by norm_num
private theorem prime_thirteenK_6563 : Nat.Prime 6563 := by norm_num
private theorem prime_thirteenK_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirteenK_7057 : Nat.Prime 7057 := by norm_num
private theorem prime_thirteenK_7069 : Nat.Prime 7069 := by norm_num
private theorem prime_thirteenK_7219 : Nat.Prime 7219 := by norm_num
private theorem prime_thirteenK_7687 : Nat.Prime 7687 := by norm_num
private theorem prime_thirteenK_8237 : Nat.Prime 8237 := by norm_num
private theorem prime_thirteenK_8287 : Nat.Prime 8287 := by norm_num
private theorem prime_thirteenK_8297 : Nat.Prime 8297 := by norm_num
private theorem prime_thirteenK_8641 : Nat.Prime 8641 := by norm_num
private theorem prime_thirteenK_9227 : Nat.Prime 9227 := by norm_num
private theorem prime_thirteenK_9437 : Nat.Prime 9437 := by norm_num
private theorem prime_thirteenK_9719 : Nat.Prime 9719 := by norm_num
private theorem prime_thirteenK_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_thirteenK_10853 : Nat.Prime 10853 := by norm_num
private theorem prime_thirteenK_10861 : Nat.Prime 10861 := by norm_num
private theorem prime_thirteenK_11159 : Nat.Prime 11159 := by norm_num
private theorem prime_thirteenK_11353 : Nat.Prime 11353 := by norm_num
private theorem prime_thirteenK_11423 : Nat.Prime 11423 := by norm_num
private theorem prime_thirteenK_11503 : Nat.Prime 11503 := by norm_num
private theorem prime_thirteenK_12101 : Nat.Prime 12101 := by norm_num
private theorem prime_thirteenK_12301 : Nat.Prime 12301 := by norm_num
private theorem prime_thirteenK_12569 : Nat.Prime 12569 := by norm_num
private theorem prime_thirteenK_12619 : Nat.Prime 12619 := by norm_num
private theorem prime_thirteenK_12697 : Nat.Prime 12697 := by norm_num
private theorem prime_thirteenK_14419 : Nat.Prime 14419 := by norm_num
private theorem prime_thirteenK_15373 : Nat.Prime 15373 := by norm_num
private theorem prime_thirteenK_15607 : Nat.Prime 15607 := by norm_num
private theorem prime_thirteenK_15809 : Nat.Prime 15809 := by norm_num
private theorem prime_thirteenK_16069 : Nat.Prime 16069 := by norm_num
private theorem prime_thirteenK_16097 : Nat.Prime 16097 := by norm_num
private theorem prime_thirteenK_16763 : Nat.Prime 16763 := by norm_num
private theorem prime_thirteenK_16979 : Nat.Prime 16979 := by norm_num
private theorem prime_thirteenK_17449 : Nat.Prime 17449 := by norm_num
private theorem prime_thirteenK_18043 : Nat.Prime 18043 := by norm_num
private theorem prime_thirteenK_19001 : Nat.Prime 19001 := by norm_num
private theorem prime_thirteenK_19231 : Nat.Prime 19231 := by norm_num
private theorem prime_thirteenK_19387 : Nat.Prime 19387 := by norm_num
private theorem prime_thirteenK_19417 : Nat.Prime 19417 := by norm_num
private theorem prime_thirteenK_19571 : Nat.Prime 19571 := by norm_num
private theorem prime_thirteenK_20023 : Nat.Prime 20023 := by norm_num
private theorem prime_thirteenK_20029 : Nat.Prime 20029 := by norm_num
private theorem prime_thirteenK_20543 : Nat.Prime 20543 := by norm_num
private theorem prime_thirteenK_20719 : Nat.Prime 20719 := by norm_num
private theorem prime_thirteenK_21019 : Nat.Prime 21019 := by norm_num
private theorem prime_thirteenK_21569 : Nat.Prime 21569 := by norm_num
private theorem prime_thirteenK_21611 : Nat.Prime 21611 := by norm_num
private theorem prime_thirteenK_21911 : Nat.Prime 21911 := by norm_num
private theorem prime_thirteenK_22109 : Nat.Prime 22109 := by norm_num
private theorem prime_thirteenK_23909 : Nat.Prime 23909 := by norm_num
private theorem prime_thirteenK_24019 : Nat.Prime 24019 := by norm_num
private theorem prime_thirteenK_25951 : Nat.Prime 25951 := by norm_num
private theorem prime_thirteenK_26263 : Nat.Prime 26263 := by norm_num
private theorem prime_thirteenK_26387 : Nat.Prime 26387 := by norm_num
private theorem prime_thirteenK_27647 : Nat.Prime 27647 := by norm_num
private theorem prime_thirteenK_28229 : Nat.Prime 28229 := by norm_num
private theorem prime_thirteenK_28351 : Nat.Prime 28351 := by norm_num
private theorem prime_thirteenK_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_thirteenK_31223 : Nat.Prime 31223 := by norm_num
private theorem prime_thirteenK_31271 : Nat.Prime 31271 := by norm_num
private theorem prime_thirteenK_31817 : Nat.Prime 31817 := by norm_num
private theorem prime_thirteenK_32029 : Nat.Prime 32029 := by norm_num
private theorem prime_thirteenK_32369 : Nat.Prime 32369 := by norm_num
private theorem prime_thirteenK_33647 : Nat.Prime 33647 := by norm_num
private theorem prime_thirteenK_33829 : Nat.Prime 33829 := by norm_num
private theorem prime_thirteenK_34361 : Nat.Prime 34361 := by norm_num
private theorem prime_thirteenK_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirteenK_35447 : Nat.Prime 35447 := by norm_num
private theorem prime_thirteenK_35573 : Nat.Prime 35573 := by norm_num
private theorem prime_thirteenK_36263 : Nat.Prime 36263 := by norm_num
private theorem prime_thirteenK_36671 : Nat.Prime 36671 := by norm_num
private theorem prime_thirteenK_37013 : Nat.Prime 37013 := by norm_num
private theorem prime_thirteenK_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirteenK_39343 : Nat.Prime 39343 := by norm_num
private theorem prime_thirteenK_39581 : Nat.Prime 39581 := by norm_num
private theorem prime_thirteenK_39791 : Nat.Prime 39791 := by norm_num
private theorem prime_thirteenK_42433 : Nat.Prime 42433 := by norm_num
private theorem prime_thirteenK_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_thirteenK_46861 : Nat.Prime 46861 := by norm_num
private theorem prime_thirteenK_47149 : Nat.Prime 47149 := by norm_num
private theorem prime_thirteenK_51343 : Nat.Prime 51343 := by norm_num
private theorem prime_thirteenK_51913 : Nat.Prime 51913 := by norm_num
private theorem prime_thirteenK_52237 : Nat.Prime 52237 := by norm_num
private theorem prime_thirteenK_55849 : Nat.Prime 55849 := by norm_num
private theorem prime_thirteenK_58153 : Nat.Prime 58153 := by norm_num
private theorem prime_thirteenK_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirteenK_64717 : Nat.Prime 64717 := by norm_num
private theorem prime_thirteenK_65713 : Nat.Prime 65713 := by norm_num
private theorem prime_thirteenK_67819 : Nat.Prime 67819 := by norm_num
private theorem prime_thirteenK_71191 : Nat.Prime 71191 := by norm_num
private theorem prime_thirteenK_74323 : Nat.Prime 74323 := by norm_num
private theorem prime_thirteenK_75557 : Nat.Prime 75557 := by norm_num
private theorem prime_thirteenK_76259 : Nat.Prime 76259 := by norm_num
private theorem prime_thirteenK_77689 : Nat.Prime 77689 := by norm_num
private theorem prime_thirteenK_83383 : Nat.Prime 83383 := by norm_num
private theorem prime_thirteenK_83621 : Nat.Prime 83621 := by norm_num
private theorem prime_thirteenK_84017 : Nat.Prime 84017 := by norm_num
private theorem prime_thirteenK_85247 : Nat.Prime 85247 := by norm_num
private theorem prime_thirteenK_85469 : Nat.Prime 85469 := by norm_num
private theorem prime_thirteenK_95083 : Nat.Prime 95083 := by norm_num
private theorem prime_thirteenK_96211 : Nat.Prime 96211 := by norm_num
private theorem prime_thirteenK_98729 : Nat.Prime 98729 := by norm_num
private theorem prime_thirteenK_115781 : Nat.Prime 115781 := by norm_num
private theorem prime_thirteenK_118691 : Nat.Prime 118691 := by norm_num
private theorem prime_thirteenK_119653 : Nat.Prime 119653 := by norm_num
private theorem prime_thirteenK_120431 : Nat.Prime 120431 := by norm_num
private theorem prime_thirteenK_123619 : Nat.Prime 123619 := by norm_num
private theorem prime_thirteenK_146173 : Nat.Prime 146173 := by norm_num
private theorem prime_thirteenK_153929 : Nat.Prime 153929 := by norm_num
private theorem prime_thirteenK_158759 : Nat.Prime 158759 := by norm_num
private theorem prime_thirteenK_161717 : Nat.Prime 161717 := by norm_num
private theorem prime_thirteenK_163741 : Nat.Prime 163741 := by norm_num
private theorem prime_thirteenK_166931 : Nat.Prime 166931 := by norm_num
private theorem prime_thirteenK_178897 : Nat.Prime 178897 := by norm_num
private theorem prime_thirteenK_196661 : Nat.Prime 196661 := by norm_num
private theorem prime_thirteenK_199181 : Nat.Prime 199181 := by norm_num
private theorem prime_thirteenK_201167 : Nat.Prime 201167 := by norm_num
private theorem prime_thirteenK_209623 : Nat.Prime 209623 := by norm_num
private theorem prime_thirteenK_225037 : Nat.Prime 225037 := by norm_num
private theorem prime_thirteenK_227873 : Nat.Prime 227873 := by norm_num
private theorem prime_thirteenK_240509 : Nat.Prime 240509 := by norm_num
private theorem prime_thirteenK_254927 : Nat.Prime 254927 := by norm_num
private theorem prime_thirteenK_256889 : Nat.Prime 256889 := by norm_num
private theorem prime_thirteenK_265247 : Nat.Prime 265247 := by norm_num
private theorem prime_thirteenK_270563 : Nat.Prime 270563 := by norm_num
private theorem prime_thirteenK_284803 : Nat.Prime 284803 := by norm_num
private theorem prime_thirteenK_286547 : Nat.Prime 286547 := by norm_num
private theorem prime_thirteenK_295333 : Nat.Prime 295333 := by norm_num
private theorem prime_thirteenK_318313 : Nat.Prime 318313 := by norm_num
private theorem prime_thirteenK_335009 : Nat.Prime 335009 := by norm_num
private theorem prime_thirteenK_341063 : Nat.Prime 341063 := by norm_num
private theorem prime_thirteenK_372023 : Nat.Prime 372023 := by norm_num
private theorem prime_thirteenK_392099 : Nat.Prime 392099 := by norm_num
private theorem prime_thirteenK_409901 : Nat.Prime 409901 := by norm_num
private theorem prime_thirteenK_413141 : Nat.Prime 413141 := by norm_num
private theorem prime_thirteenK_427681 : Nat.Prime 427681 := by norm_num
private theorem prime_thirteenK_488321 : Nat.Prime 488321 := by norm_num
private theorem prime_thirteenK_520043 : Nat.Prime 520043 := by norm_num
private theorem prime_thirteenK_556859 : Nat.Prime 556859 := by norm_num
private theorem prime_thirteenK_558979 : Nat.Prime 558979 := by norm_num
private theorem prime_thirteenK_560213 : Nat.Prime 560213 := by norm_num
private theorem prime_thirteenK_580169 : Nat.Prime 580169 := by norm_num
private theorem prime_thirteenK_617249 : Nat.Prime 617249 := by norm_num
private theorem prime_thirteenK_652081 : Nat.Prime 652081 := by norm_num
private theorem prime_thirteenK_657653 : Nat.Prime 657653 := by norm_num
private theorem prime_thirteenK_667123 : Nat.Prime 667123 := by norm_num
private theorem prime_thirteenK_759313 : Nat.Prime 759313 := by norm_num
private theorem prime_thirteenK_785903 : Nat.Prime 785903 := by norm_num
private theorem prime_thirteenK_873113 : Nat.Prime 873113 := by norm_num
private theorem prime_thirteenK_873139 : Nat.Prime 873139 := by norm_num
private theorem prime_thirteenK_908317 : Nat.Prime 908317 := by norm_num
private theorem prime_thirteenK_912631 : Nat.Prime 912631 := by norm_num
private theorem prime_thirteenK_923579 : Nat.Prime 923579 := by norm_num
private theorem prime_thirteenK_934517 : Nat.Prime 934517 := by norm_num
private theorem prime_thirteenK_955337 : Nat.Prime 955337 := by norm_num
private theorem prime_thirteenK_970687 : Nat.Prime 970687 := by norm_num
private theorem prime_thirteenK_1000981 : Nat.Prime 1000981 := by norm_num
private theorem prime_thirteenK_1029563 : Nat.Prime 1029563 := by norm_num
private theorem prime_thirteenK_1093943 : Nat.Prime 1093943 := by norm_num
private theorem prime_thirteenK_1195031 : Nat.Prime 1195031 := by norm_num
private theorem prime_thirteenK_1288247 : Nat.Prime 1288247 := by norm_num
private theorem prime_thirteenK_1355153 : Nat.Prime 1355153 := by norm_num
private theorem prime_thirteenK_1430543 : Nat.Prime 1430543 := by norm_num
private theorem prime_thirteenK_1547593 : Nat.Prime 1547593 := by norm_num
private theorem prime_thirteenK_1582963 : Nat.Prime 1582963 := by norm_num
private theorem prime_thirteenK_1584001 : Nat.Prime 1584001 := by norm_num
private theorem prime_thirteenK_1602863 : Nat.Prime 1602863 := by norm_num
private theorem prime_thirteenK_1628203 : Nat.Prime 1628203 := by norm_num
private theorem prime_thirteenK_1648531 : Nat.Prime 1648531 := by norm_num
private theorem prime_thirteenK_1849103 : Nat.Prime 1849103 := by norm_num
private theorem prime_thirteenK_1921687 : Nat.Prime 1921687 := by norm_num
private theorem prime_thirteenK_1958641 : Nat.Prime 1958641 := by norm_num
private theorem prime_thirteenK_2102851 : Nat.Prime 2102851 := by norm_num
private theorem prime_thirteenK_2220277 : Nat.Prime 2220277 := by norm_num
private theorem prime_thirteenK_2273119 : Nat.Prime 2273119 := by norm_num
private theorem prime_thirteenK_2410589 : Nat.Prime 2410589 := by norm_num
private theorem prime_thirteenK_2596501 : Nat.Prime 2596501 := by norm_num
private theorem prime_thirteenK_2762741 : Nat.Prime 2762741 := by norm_num
private theorem prime_thirteenK_3089857 : Nat.Prime 3089857 := by norm_num
private theorem prime_thirteenK_3225139 : Nat.Prime 3225139 := by norm_num
private theorem prime_thirteenK_3399569 : Nat.Prime 3399569 := by norm_num
private theorem prime_thirteenK_3429287 : Nat.Prime 3429287 := by norm_num
private theorem prime_thirteenK_3492397 : Nat.Prime 3492397 := by norm_num
private theorem prime_thirteenK_3720487 : Nat.Prime 3720487 := by norm_num
private theorem prime_thirteenK_3964613 : Nat.Prime 3964613 := by norm_num
private theorem prime_thirteenK_4391371 : Nat.Prime 4391371 := by norm_num
private theorem prime_thirteenK_4553573 : Nat.Prime 4553573 := by norm_num
private theorem prime_thirteenK_5037757 : Nat.Prime 5037757 := by norm_num
private theorem prime_thirteenK_5082277 : Nat.Prime 5082277 := by norm_num
private theorem prime_thirteenK_5140117 : Nat.Prime 5140117 := by norm_num
private theorem prime_thirteenK_5309207 : Nat.Prime 5309207 := by norm_num
private theorem prime_thirteenK_6132143 : Nat.Prime 6132143 := by norm_num
private theorem prime_thirteenK_6548263 : Nat.Prime 6548263 := by norm_num
private theorem prime_thirteenK_7027961 : Nat.Prime 7027961 := by norm_num
private theorem prime_thirteenK_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirteenK_8132653 : Nat.Prime 8132653 := by norm_num
private theorem prime_thirteenK_8270923 : Nat.Prime 8270923 := by norm_num
private theorem prime_thirteenK_8562377 : Nat.Prime 8562377 := by norm_num
private theorem prime_thirteenK_8687729 : Nat.Prime 8687729 := by norm_num
private theorem prime_thirteenK_9269333 : Nat.Prime 9269333 := by norm_num
private theorem prime_thirteenK_9441539 : Nat.Prime 9441539 := by norm_num
private theorem prime_thirteenK_9445537 : Nat.Prime 9445537 := by norm_num
private theorem prime_thirteenK_10537391 : Nat.Prime 10537391 := by norm_num
private theorem prime_thirteenK_10801067 : Nat.Prime 10801067 := by norm_num
private theorem prime_thirteenK_13116839 : Nat.Prime 13116839 := by norm_num
private theorem prime_thirteenK_14457413 : Nat.Prime 14457413 := by norm_num
private theorem prime_thirteenK_14751743 : Nat.Prime 14751743 := by norm_num
private theorem prime_thirteenK_14989397 : Nat.Prime 14989397 := by norm_num
private theorem prime_thirteenK_14994619 : Nat.Prime 14994619 := by norm_num
private theorem prime_thirteenK_17325551 : Nat.Prime 17325551 := by norm_num
private theorem prime_thirteenK_18915877 : Nat.Prime 18915877 := by norm_num
private theorem prime_thirteenK_19050289 : Nat.Prime 19050289 := by norm_num
private theorem prime_thirteenK_19382141 : Nat.Prime 19382141 := by norm_num
private theorem prime_thirteenK_20930737 : Nat.Prime 20930737 := by norm_num
private theorem prime_thirteenK_22420633 : Nat.Prime 22420633 := by norm_num
private theorem prime_thirteenK_22724479 : Nat.Prime 22724479 := by norm_num
private theorem prime_thirteenK_24484021 : Nat.Prime 24484021 := by norm_num
private theorem prime_thirteenK_26281223 : Nat.Prime 26281223 := by norm_num
private theorem prime_thirteenK_27101549 : Nat.Prime 27101549 := by norm_num
private theorem prime_thirteenK_27509047 : Nat.Prime 27509047 := by norm_num

private theorem prime_thirteenK_31784387 : Nat.Prime 31784387 := by
  apply lucas_primality 31784387 (2 : ZMod 31784387)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (201167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (201167, 1)] : List FactorBlock).map factorBlockValue).prod) = 31784387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_79
      · exact prime_thirteenK_201167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31784387) ^ 15892193 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31784387) ^ 402334 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31784387) ^ 158 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_32251391 : Nat.Prime 32251391 := by
  apply lucas_primality 32251391 (7 : ZMod 32251391)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3225139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3225139, 1)] : List FactorBlock).map factorBlockValue).prod) = 32251391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_3225139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 32251391) ^ 16125695 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 32251391) ^ 6450278 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 32251391) ^ 10 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_33642613 : Nat.Prime 33642613 := by
  apply lucas_primality 33642613 (5 : ZMod 33642613)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (934517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (934517, 1)] : List FactorBlock).map factorBlockValue).prod) = 33642613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_934517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33642613) ^ 16821306 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 33642613) ^ 11214204 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 33642613) ^ 36 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_35864239 : Nat.Prime 35864239 := by
  apply lucas_primality 35864239 (3 : ZMod 35864239)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (36671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (36671, 1)] : List FactorBlock).map factorBlockValue).prod) = 35864239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_163
      · exact prime_thirteenK_36671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35864239) ^ 17932119 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35864239) ^ 11954746 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35864239) ^ 220026 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35864239) ^ 978 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_39198199 : Nat.Prime 39198199 := by
  apply lucas_primality 39198199 (6 : ZMod 39198199)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (29, 1), (31, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (29, 1), (31, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) = 39198199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_29
      · exact prime_thirteenK_31
      · exact prime_thirteenK_43
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 39198199) ^ 19599099 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 13066066 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 3015246 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 1351662 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 1264458 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 39198199) ^ 911586 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_39730861 : Nat.Prime 39730861 := by
  apply lucas_primality 39730861 (2 : ZMod 39730861)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (16979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (16979, 1)] : List FactorBlock).map factorBlockValue).prod) = 39730861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_13
      · exact prime_thirteenK_16979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39730861) ^ 19865430 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39730861) ^ 13243620 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39730861) ^ 7946172 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39730861) ^ 3056220 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 39730861) ^ 2340 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_46053307 : Nat.Prime 46053307 := by
  apply lucas_primality 46053307 (2 : ZMod 46053307)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (17, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (17, 2), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 46053307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46053307) ^ 23026653 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 15351102 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 3542562 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 2709018 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46053307) ^ 202878 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_53780449 : Nat.Prime 53780449 := by
  apply lucas_primality 53780449 (11 : ZMod 53780449)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (560213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (560213, 1)] : List FactorBlock).map factorBlockValue).prod) = 53780449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_560213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 53780449) ^ 26890224 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 53780449) ^ 17926816 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 53780449) ^ 96 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_58233559 : Nat.Prime 58233559 := by
  apply lucas_primality 58233559 (6 : ZMod 58233559)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1933, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1933, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) = 58233559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_1933
      · exact prime_thirteenK_5021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 58233559) ^ 29116779 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 58233559) ^ 19411186 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 58233559) ^ 30126 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 58233559) ^ 11598 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_60064987 : Nat.Prime 60064987 := by
  apply lucas_primality 60064987 (3 : ZMod 60064987)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (270563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (270563, 1)] : List FactorBlock).map factorBlockValue).prod) = 60064987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_37
      · exact prime_thirteenK_270563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 60064987) ^ 30032493 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60064987) ^ 20021662 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60064987) ^ 1623378 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60064987) ^ 222 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_63416971 : Nat.Prime 63416971 := by
  apply lucas_primality 63416971 (2 : ZMod 63416971)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (181, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (181, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) = 63416971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_17
      · exact prime_thirteenK_181
      · exact prime_thirteenK_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63416971) ^ 31708485 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 21138990 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 12683394 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 3730410 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 350370 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 63416971) ^ 276930 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_64502783 : Nat.Prime 64502783 := by
  apply lucas_primality 64502783 (5 : ZMod 64502783)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32251391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32251391, 1)] : List FactorBlock).map factorBlockValue).prod) = 64502783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_32251391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64502783) ^ 32251391 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 64502783) ^ 2 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_64898749 : Nat.Prime 64898749 := by
  apply lucas_primality 64898749 (6 : ZMod 64898749)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (58153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (58153, 1)] : List FactorBlock).map factorBlockValue).prod) = 64898749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_31
      · exact prime_thirteenK_58153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 64898749) ^ 32449374 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 64898749) ^ 21632916 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 64898749) ^ 2093508 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 64898749) ^ 1116 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_64938073 : Nat.Prime 64938073 := by
  apply lucas_primality 64938073 (5 : ZMod 64938073)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1327, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1327, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) = 64938073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_1327
      · exact prime_thirteenK_2039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64938073) ^ 32469036 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 64938073) ^ 21646024 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 64938073) ^ 48936 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 64938073) ^ 31848 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_68392019 : Nat.Prime 68392019 := by
  apply lucas_primality 68392019 (2 : ZMod 68392019)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (36263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (36263, 1)] : List FactorBlock).map factorBlockValue).prod) = 68392019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_23
      · exact prime_thirteenK_41
      · exact prime_thirteenK_36263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68392019) ^ 34196009 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 2973566 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 1668098 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68392019) ^ 1886 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_76054961 : Nat.Prime 76054961 := by
  apply lucas_primality 76054961 (3 : ZMod 76054961)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (43, 1), (22109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (43, 1), (22109, 1)] : List FactorBlock).map factorBlockValue).prod) = 76054961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_43
      · exact prime_thirteenK_22109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 76054961) ^ 38027480 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 76054961) ^ 15210992 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 76054961) ^ 1768720 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 76054961) ^ 3440 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_80219981 : Nat.Prime 80219981 := by
  apply lucas_primality 80219981 (2 : ZMod 80219981)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (257, 1), (15607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (257, 1), (15607, 1)] : List FactorBlock).map factorBlockValue).prod) = 80219981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_257
      · exact prime_thirteenK_15607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80219981) ^ 40109990 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 16043996 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 312140 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 80219981) ^ 5140 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_82882231 : Nat.Prime 82882231 := by
  apply lucas_primality 82882231 (6 : ZMod 82882231)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2762741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2762741, 1)] : List FactorBlock).map factorBlockValue).prod) = 82882231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_2762741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 82882231) ^ 41441115 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 82882231) ^ 27627410 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 82882231) ^ 16576446 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 82882231) ^ 30 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_83511149 : Nat.Prime 83511149 := by
  apply lucas_primality 83511149 (2 : ZMod 83511149)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (96211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (96211, 1)] : List FactorBlock).map factorBlockValue).prod) = 83511149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_31
      · exact prime_thirteenK_96211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83511149) ^ 41755574 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 11930164 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 2693908 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83511149) ^ 868 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_86356709 : Nat.Prime 86356709 := by
  apply lucas_primality 86356709 (2 : ZMod 86356709)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2621, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2621, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) = 86356709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_2621
      · exact prime_thirteenK_8237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86356709) ^ 43178354 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 86356709) ^ 32948 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 86356709) ^ 10484 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_88986923 : Nat.Prime 88986923 := by
  apply lucas_primality 88986923 (2 : ZMod 88986923)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (653, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (653, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) = 88986923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_61
      · exact prime_thirteenK_653
      · exact prime_thirteenK_1117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 88986923) ^ 44493461 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88986923) ^ 1458802 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88986923) ^ 136274 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 88986923) ^ 79666 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_89131981 : Nat.Prime 89131981 := by
  apply lucas_primality 89131981 (6 : ZMod 89131981)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 3), (61, 1), (71, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 3), (61, 1), (71, 1)] : List FactorBlock).map factorBlockValue).prod) = 89131981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_61
      · exact prime_thirteenK_71
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 89131981) ^ 44565990 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89131981) ^ 29710660 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89131981) ^ 17826396 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89131981) ^ 12733140 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89131981) ^ 1461180 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 89131981) ^ 1255380 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_90218467 : Nat.Prime 90218467 := by
  apply lucas_primality 90218467 (2 : ZMod 90218467)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (23, 1), (16763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (23, 1), (16763, 1)] : List FactorBlock).map factorBlockValue).prod) = 90218467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_23
      · exact prime_thirteenK_16763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90218467) ^ 45109233 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 90218467) ^ 30072822 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 90218467) ^ 6939882 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 90218467) ^ 3922542 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 90218467) ^ 5382 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_97327729 : Nat.Prime 97327729 := by
  apply lucas_primality 97327729 (37 : ZMod 97327729)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (35573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (35573, 1)] : List FactorBlock).map factorBlockValue).prod) = 97327729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_19
      · exact prime_thirteenK_35573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (37 : ZMod 97327729) ^ 48663864 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (37 : ZMod 97327729) ^ 32442576 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (37 : ZMod 97327729) ^ 5122512 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (37 : ZMod 97327729) ^ 2736 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_105309793 : Nat.Prime 105309793 := by
  apply lucas_primality 105309793 (5 : ZMod 105309793)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (52237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (52237, 1)] : List FactorBlock).map factorBlockValue).prod) = 105309793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_52237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 105309793) ^ 52654896 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 105309793) ^ 35103264 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 105309793) ^ 15044256 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 105309793) ^ 2016 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_116997143 : Nat.Prime 116997143 := by
  apply lucas_primality 116997143 (5 : ZMod 116997143)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) = 116997143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_67
      · exact prime_thirteenK_873113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 116997143) ^ 58498571 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 116997143) ^ 1746226 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 116997143) ^ 134 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_118081211 : Nat.Prime 118081211 := by
  apply lucas_primality 118081211 (14 : ZMod 118081211)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (908317, 1)] : List FactorBlock).map factorBlockValue).prod) = 118081211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_13
      · exact prime_thirteenK_908317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 118081211) ^ 59040605 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 23616242 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 9083170 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 118081211) ^ 130 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_118535279 : Nat.Prime 118535279 := by
  apply lucas_primality 118535279 (7 : ZMod 118535279)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1831, 1), (32369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1831, 1), (32369, 1)] : List FactorBlock).map factorBlockValue).prod) = 118535279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_1831
      · exact prime_thirteenK_32369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 118535279) ^ 59267639 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 118535279) ^ 64738 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 118535279) ^ 3662 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_148272073 : Nat.Prime 148272073 := by
  apply lucas_primality 148272073 (5 : ZMod 148272073)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (41, 1), (67, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (41, 1), (67, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 148272073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_41
      · exact prime_thirteenK_67
      · exact prime_thirteenK_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 148272073) ^ 74136036 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 49424024 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 11405544 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 3616392 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 2213016 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 148272073) ^ 857064 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_158288029 : Nat.Prime 158288029 := by
  apply lucas_primality 158288029 (6 : ZMod 158288029)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (84017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (84017, 1)] : List FactorBlock).map factorBlockValue).prod) = 158288029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_157
      · exact prime_thirteenK_84017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 158288029) ^ 79144014 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 52762676 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 1008204 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 158288029) ^ 1884 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_160439963 : Nat.Prime 160439963 := by
  apply lucas_primality 160439963 (2 : ZMod 160439963)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80219981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80219981, 1)] : List FactorBlock).map factorBlockValue).prod) = 160439963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_80219981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 160439963) ^ 80219981 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160439963) ^ 2 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_164681581 : Nat.Prime 164681581 := by
  apply lucas_primality 164681581 (10 : ZMod 164681581)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) = 164681581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_392099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 164681581) ^ 82340790 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 54893860 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 32936316 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 23525940 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 164681581) ^ 420 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_168197789 : Nat.Prime 168197789 := by
  apply lucas_primality 168197789 (2 : ZMod 168197789)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (113, 1), (33829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (113, 1), (33829, 1)] : List FactorBlock).map factorBlockValue).prod) = 168197789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_11
      · exact prime_thirteenK_113
      · exact prime_thirteenK_33829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 168197789) ^ 84098894 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 15290708 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 1488476 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 168197789) ^ 4972 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_189673039 : Nat.Prime 189673039 := by
  apply lucas_primality 189673039 (3 : ZMod 189673039)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (10537391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (10537391, 1)] : List FactorBlock).map factorBlockValue).prod) = 189673039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_10537391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 189673039) ^ 94836519 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 189673039) ^ 63224346 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 189673039) ^ 18 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_190277159 : Nat.Prime 190277159 := by
  apply lucas_primality 190277159 (7 : ZMod 190277159)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (109, 1), (51343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (109, 1), (51343, 1)] : List FactorBlock).map factorBlockValue).prod) = 190277159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_17
      · exact prime_thirteenK_109
      · exact prime_thirteenK_51343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 190277159) ^ 95138579 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 190277159) ^ 11192774 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 190277159) ^ 1745662 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 190277159) ^ 3706 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_209451817 : Nat.Prime 209451817 := by
  apply lucas_primality 209451817 (5 : ZMod 209451817)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (157, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (157, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) = 209451817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_157
      · exact prime_thirteenK_2647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 209451817) ^ 104725908 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 209451817) ^ 69817272 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 209451817) ^ 29921688 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 209451817) ^ 1334088 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 209451817) ^ 79128 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_220118471 : Nat.Prime 220118471 := by
  apply lucas_primality 220118471 (11 : ZMod 220118471)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (153929, 1)] : List FactorBlock).map factorBlockValue).prod) = 220118471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_153929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 220118471) ^ 110059235 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 44023694 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 20010770 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 16932190 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 220118471) ^ 1430 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_240259949 : Nat.Prime 240259949 := by
  apply lucas_primality 240259949 (2 : ZMod 240259949)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (60064987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (60064987, 1)] : List FactorBlock).map factorBlockValue).prod) = 240259949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_60064987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 240259949) ^ 120129974 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 240259949) ^ 4 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_244201109 : Nat.Prime 244201109 := by
  apply lucas_primality 244201109 (2 : ZMod 244201109)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (341063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (341063, 1)] : List FactorBlock).map factorBlockValue).prod) = 244201109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_179
      · exact prime_thirteenK_341063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 244201109) ^ 122100554 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 244201109) ^ 1364252 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 244201109) ^ 716 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_292379671 : Nat.Prime 292379671 := by
  apply lucas_primality 292379671 (6 : ZMod 292379671)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (295333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (295333, 1)] : List FactorBlock).map factorBlockValue).prod) = 292379671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_11
      · exact prime_thirteenK_295333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 292379671) ^ 146189835 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 292379671) ^ 97459890 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 292379671) ^ 58475934 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 292379671) ^ 26579970 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 292379671) ^ 990 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_320879927 : Nat.Prime 320879927 := by
  apply lucas_primality 320879927 (5 : ZMod 320879927)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (160439963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (160439963, 1)] : List FactorBlock).map factorBlockValue).prod) = 320879927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_160439963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 320879927) ^ 160439963 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 320879927) ^ 2 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_360347051 : Nat.Prime 360347051 := by
  apply lucas_primality 360347051 (2 : ZMod 360347051)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (1029563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (1029563, 1)] : List FactorBlock).map factorBlockValue).prod) = 360347051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_1029563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 360347051) ^ 180173525 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 72069410 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 51478150 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 360347051) ^ 350 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_384436501 : Nat.Prime 384436501 := by
  apply lucas_primality 384436501 (17 : ZMod 384436501)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (7, 1), (19, 1), (41, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (7, 1), (19, 1), (41, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 384436501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_19
      · exact prime_thirteenK_41
      · exact prime_thirteenK_47
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 384436501) ^ 192218250 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 384436501) ^ 128145500 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 384436501) ^ 76887300 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 384436501) ^ 54919500 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 384436501) ^ 20233500 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 384436501) ^ 9376500 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 384436501) ^ 8179500 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_429845593 : Nat.Prime 429845593 := by
  apply lucas_primality 429845593 (5 : ZMod 429845593)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (1628203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (1628203, 1)] : List FactorBlock).map factorBlockValue).prod) = 429845593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_1628203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 429845593) ^ 214922796 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 143281864 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 39076872 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 429845593) ^ 264 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_439799513 : Nat.Prime 439799513 := by
  apply lucas_primality 439799513 (3 : ZMod 439799513)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 2), (19571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 2), (19571, 1)] : List FactorBlock).map factorBlockValue).prod) = 439799513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_53
      · exact prime_thirteenK_19571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 439799513) ^ 219899756 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 439799513) ^ 8298104 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 439799513) ^ 22472 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_440144753 : Nat.Prime 440144753 := by
  apply lucas_primality 440144753 (3 : ZMod 440144753)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (27509047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (27509047, 1)] : List FactorBlock).map factorBlockValue).prod) = 440144753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_27509047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 440144753) ^ 220072376 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 440144753) ^ 16 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_474047419 : Nat.Prime 474047419 := by
  apply lucas_primality 474047419 (14 : ZMod 474047419)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (59, 1), (239, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (59, 1), (239, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 474047419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_59
      · exact prime_thirteenK_239
      · exact prime_thirteenK_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 474047419) ^ 237023709 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 474047419) ^ 158015806 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 474047419) ^ 36465186 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 474047419) ^ 8034702 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 474047419) ^ 1983462 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 474047419) ^ 1099878 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_518925343 : Nat.Prime 518925343 := by
  apply lucas_primality 518925343 (3 : ZMod 518925343)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (613, 1), (10853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (613, 1), (10853, 1)] : List FactorBlock).map factorBlockValue).prod) = 518925343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_613
      · exact prime_thirteenK_10853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 518925343) ^ 259462671 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 518925343) ^ 172975114 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 518925343) ^ 39917334 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 518925343) ^ 846534 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 518925343) ^ 47814 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_562403069 : Nat.Prime 562403069 := by
  apply lucas_primality 562403069 (2 : ZMod 562403069)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (3429287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (3429287, 1)] : List FactorBlock).map factorBlockValue).prod) = 562403069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_41
      · exact prime_thirteenK_3429287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 562403069) ^ 281201534 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 562403069) ^ 13717148 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 562403069) ^ 164 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_611666813 : Nat.Prime 611666813 := by
  apply lucas_primality 611666813 (2 : ZMod 611666813)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1237, 1), (123619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1237, 1), (123619, 1)] : List FactorBlock).map factorBlockValue).prod) = 611666813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_1237
      · exact prime_thirteenK_123619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 611666813) ^ 305833406 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 611666813) ^ 494476 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 611666813) ^ 4948 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_626080687 : Nat.Prime 626080687 := by
  apply lucas_primality 626080687 (5 : ZMod 626080687)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (1355153, 1)] : List FactorBlock).map factorBlockValue).prod) = 626080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_1355153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626080687) ^ 313040343 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 208693562 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 89440098 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 56916426 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 626080687) ^ 462 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_671643431 : Nat.Prime 671643431 := by
  apply lucas_primality 671643431 (7 : ZMod 671643431)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (103, 1), (652081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (103, 1), (652081, 1)] : List FactorBlock).map factorBlockValue).prod) = 671643431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_103
      · exact prime_thirteenK_652081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 671643431) ^ 335821715 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 671643431) ^ 134328686 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 671643431) ^ 6520810 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 671643431) ^ 1030 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_687061883 : Nat.Prime 687061883 := by
  apply lucas_primality 687061883 (2 : ZMod 687061883)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (83, 1), (181, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (83, 1), (181, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod) = 687061883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_83
      · exact prime_thirteenK_181
      · exact prime_thirteenK_1759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 687061883) ^ 343530941 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 687061883) ^ 52850914 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 687061883) ^ 8277854 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 687061883) ^ 3795922 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 687061883) ^ 390598 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_688371109 : Nat.Prime 688371109 := by
  apply lucas_primality 688371109 (2 : ZMod 688371109)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6217, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6217, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) = 688371109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_6217
      · exact prime_thirteenK_9227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 688371109) ^ 344185554 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 688371109) ^ 229457036 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 688371109) ^ 110724 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 688371109) ^ 74604 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_721908347 : Nat.Prime 721908347 := by
  apply lucas_primality 721908347 (2 : ZMod 721908347)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (487, 1), (23909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (487, 1), (23909, 1)] : List FactorBlock).map factorBlockValue).prod) = 721908347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_31
      · exact prime_thirteenK_487
      · exact prime_thirteenK_23909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 721908347) ^ 360954173 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 721908347) ^ 23287366 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 721908347) ^ 1482358 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 721908347) ^ 30194 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_752335981 : Nat.Prime 752335981 := by
  apply lucas_primality 752335981 (6 : ZMod 752335981)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (29, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (29, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) = 752335981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_11
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_1709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 752335981) ^ 376167990 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 250778660 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 150467196 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 68394180 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 32710260 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 25942620 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 752335981) ^ 440220 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_758692157 : Nat.Prime 758692157 := by
  apply lucas_primality 758692157 (2 : ZMod 758692157)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (189673039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (189673039, 1)] : List FactorBlock).map factorBlockValue).prod) = 758692157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_189673039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 758692157) ^ 379346078 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 758692157) ^ 4 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_821246401 : Nat.Prime 821246401 := by
  apply lucas_primality 821246401 (7 : ZMod 821246401)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (13, 1), (41, 1), (107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (13, 1), (41, 1), (107, 1)] : List FactorBlock).map factorBlockValue).prod) = 821246401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_13
      · exact prime_thirteenK_41
      · exact prime_thirteenK_107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 821246401) ^ 410623200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 821246401) ^ 273748800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 821246401) ^ 164249280 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 821246401) ^ 63172800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 821246401) ^ 20030400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 821246401) ^ 7675200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1028328883 : Nat.Prime 1028328883 := by
  apply lucas_primality 1028328883 (2 : ZMod 1028328883)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (24484021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (24484021, 1)] : List FactorBlock).map factorBlockValue).prod) = 1028328883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_24484021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1028328883) ^ 514164441 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1028328883) ^ 342776294 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1028328883) ^ 146904126 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1028328883) ^ 42 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1160494157 : Nat.Prime 1160494157 := by
  apply lucas_primality 1160494157 (2 : ZMod 1160494157)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (521, 1), (556859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (521, 1), (556859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160494157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_521
      · exact prime_thirteenK_556859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1160494157) ^ 580247078 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160494157) ^ 2227436 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1160494157) ^ 2084 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_29
      · exact prime_thirteenK_113
      · exact prime_thirteenK_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1317915923 : Nat.Prime 1317915923 := by
  apply lucas_primality 1317915923 (2 : ZMod 1317915923)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (313, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (313, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1317915923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_17
      · exact prime_thirteenK_59
      · exact prime_thirteenK_313
      · exact prime_thirteenK_2099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1317915923) ^ 658957961 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 77524466 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 22337558 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 4210594 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1317915923) ^ 627878 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1474306679 : Nat.Prime 1474306679 := by
  apply lucas_primality 1474306679 (17 : ZMod 1474306679)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (127, 1), (457, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (127, 1), (457, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474306679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_127
      · exact prime_thirteenK_457
      · exact prime_thirteenK_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1474306679) ^ 737153339 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 113408206 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 11608714 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 3226054 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1474306679) ^ 1509014 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1527929617 : Nat.Prime 1527929617 := by
  apply lucas_primality 1527929617 (13 : ZMod 1527929617)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (101, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (101, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) = 1527929617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_41
      · exact prime_thirteenK_101
      · exact prime_thirteenK_7687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1527929617) ^ 763964808 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1527929617) ^ 509309872 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1527929617) ^ 37266576 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1527929617) ^ 15128016 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1527929617) ^ 198768 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2281358881 : Nat.Prime 2281358881 := by
  apply lucas_primality 2281358881 (11 : ZMod 2281358881)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (19, 1), (83383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (19, 1), (83383, 1)] : List FactorBlock).map factorBlockValue).prod) = 2281358881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_19
      · exact prime_thirteenK_83383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2281358881) ^ 1140679440 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2281358881) ^ 760452960 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2281358881) ^ 456271776 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2281358881) ^ 120071520 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 2281358881) ^ 27360 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2392239617 : Nat.Prime 2392239617 := by
  apply lucas_primality 2392239617 (3 : ZMod 2392239617)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (13, 2), (27647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (13, 2), (27647, 1)] : List FactorBlock).map factorBlockValue).prod) = 2392239617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_27647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2392239617) ^ 1196119808 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2392239617) ^ 184018432 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2392239617) ^ 86528 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2582225209 : Nat.Prime 2582225209 := by
  apply lucas_primality 2582225209 (13 : ZMod 2582225209)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (35864239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (35864239, 1)] : List FactorBlock).map factorBlockValue).prod) = 2582225209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_35864239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 2582225209) ^ 1291112604 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 2582225209) ^ 860741736 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 2582225209) ^ 72 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_4430215469 : Nat.Prime 4430215469 := by
  apply lucas_primality 4430215469 (2 : ZMod 4430215469)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (163, 1), (970687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (163, 1), (970687, 1)] : List FactorBlock).map factorBlockValue).prod) = 4430215469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_163
      · exact prime_thirteenK_970687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4430215469) ^ 2215107734 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4430215469) ^ 632887924 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4430215469) ^ 27179236 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4430215469) ^ 4564 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_4499780951 : Nat.Prime 4499780951 := by
  apply lucas_primality 4499780951 (7 : ZMod 4499780951)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (558979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (558979, 1)] : List FactorBlock).map factorBlockValue).prod) = 4499780951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_23
      · exact prime_thirteenK_558979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4499780951) ^ 2249890475 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 899956190 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 642825850 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 195642650 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4499780951) ^ 8050 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_4598633189 : Nat.Prime 4598633189 := by
  apply lucas_primality 4598633189 (2 : ZMod 4598633189)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (8270923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (8270923, 1)] : List FactorBlock).map factorBlockValue).prod) = 4598633189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_139
      · exact prime_thirteenK_8270923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4598633189) ^ 2299316594 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4598633189) ^ 33083692 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4598633189) ^ 556 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_4967477161 : Nat.Prime 4967477161 := by
  apply lucas_primality 4967477161 (7 : ZMod 4967477161)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (163, 1), (229, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (163, 1), (229, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 4967477161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_163
      · exact prime_thirteenK_229
      · exact prime_thirteenK_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4967477161) ^ 2483738580 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4967477161) ^ 1655825720 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4967477161) ^ 993495432 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4967477161) ^ 30475320 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4967477161) ^ 21692040 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4967477161) ^ 4479240 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_5327453741 : Nat.Prime 5327453741 := by
  apply lucas_primality 5327453741 (2 : ZMod 5327453741)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (499, 1), (76259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (499, 1), (76259, 1)] : List FactorBlock).map factorBlockValue).prod) = 5327453741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_499
      · exact prime_thirteenK_76259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5327453741) ^ 2663726870 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 1065490748 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 761064820 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 10676260 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5327453741) ^ 69860 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_5834431507 : Nat.Prime 5834431507 := by
  apply lucas_primality 5834431507 (2 : ZMod 5834431507)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (26281223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (26281223, 1)] : List FactorBlock).map factorBlockValue).prod) = 5834431507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_37
      · exact prime_thirteenK_26281223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5834431507) ^ 2917215753 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 1944810502 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 157687338 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5834431507) ^ 222 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_6677766077 : Nat.Prime 6677766077 := by
  apply lucas_primality 6677766077 (2 : ZMod 6677766077)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (39343, 1), (42433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (39343, 1), (42433, 1)] : List FactorBlock).map factorBlockValue).prod) = 6677766077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_39343
      · exact prime_thirteenK_42433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6677766077) ^ 3338883038 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6677766077) ^ 169732 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6677766077) ^ 157372 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_6856603493 : Nat.Prime 6856603493 := by
  apply lucas_primality 6856603493 (2 : ZMod 6856603493)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (90218467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (90218467, 1)] : List FactorBlock).map factorBlockValue).prod) = 6856603493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_19
      · exact prime_thirteenK_90218467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6856603493) ^ 3428301746 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856603493) ^ 360873868 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6856603493) ^ 76 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_6910156909 : Nat.Prime 6910156909 := by
  apply lucas_primality 6910156909 (2 : ZMod 6910156909)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (149, 1), (1288247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (149, 1), (1288247, 1)] : List FactorBlock).map factorBlockValue).prod) = 6910156909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_149
      · exact prime_thirteenK_1288247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6910156909) ^ 3455078454 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6910156909) ^ 2303385636 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6910156909) ^ 46376892 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6910156909) ^ 5364 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_9144957047 : Nat.Prime 9144957047 := by
  apply lucas_primality 9144957047 (5 : ZMod 9144957047)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1229, 1), (3720487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1229, 1), (3720487, 1)] : List FactorBlock).map factorBlockValue).prod) = 9144957047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_1229
      · exact prime_thirteenK_3720487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9144957047) ^ 4572478523 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9144957047) ^ 7440974 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9144957047) ^ 2458 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_9456603047 : Nat.Prime 9456603047 := by
  apply lucas_primality 9456603047 (5 : ZMod 9456603047)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (429845593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (429845593, 1)] : List FactorBlock).map factorBlockValue).prod) = 9456603047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_11
      · exact prime_thirteenK_429845593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9456603047) ^ 4728301523 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9456603047) ^ 859691186 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9456603047) ^ 22 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_9681677849 : Nat.Prime 9681677849 := by
  apply lucas_primality 9681677849 (3 : ZMod 9681677849)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (389, 1), (163741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (389, 1), (163741, 1)] : List FactorBlock).map factorBlockValue).prod) = 9681677849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_19
      · exact prime_thirteenK_389
      · exact prime_thirteenK_163741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9681677849) ^ 4840838924 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9681677849) ^ 509561992 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9681677849) ^ 24888632 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9681677849) ^ 59128 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_11928834361 : Nat.Prime 11928834361 := by
  apply lucas_primality 11928834361 (7 : ZMod 11928834361)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (211, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (211, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) = 11928834361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_211
      · exact prime_thirteenK_17449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11928834361) ^ 5964417180 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 3976278120 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 2385766872 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 56534760 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 11928834361) ^ 683640 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_13001360959 : Nat.Prime 13001360959 := by
  apply lucas_primality 13001360959 (3 : ZMod 13001360959)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (229, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (229, 1), (85247, 1)] : List FactorBlock).map factorBlockValue).prod) = 13001360959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_37
      · exact prime_thirteenK_229
      · exact prime_thirteenK_85247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13001360959) ^ 6500680479 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 4333786986 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 351388134 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 56774502 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13001360959) ^ 152514 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_13492702567 : Nat.Prime 13492702567 := by
  apply lucas_primality 13492702567 (3 : ZMod 13492702567)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 2), (47, 1), (59, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 13492702567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_23
      · exact prime_thirteenK_47
      · exact prime_thirteenK_59
      · exact prime_thirteenK_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13492702567) ^ 6746351283 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 4497567522 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 1927528938 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 586639242 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 287078778 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 228689874 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 13492702567) ^ 184831542 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_15166086619 : Nat.Prime 15166086619 := by
  apply lucas_primality 15166086619 (2 : ZMod 15166086619)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (53780449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (53780449, 1)] : List FactorBlock).map factorBlockValue).prod) = 15166086619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53780449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15166086619) ^ 7583043309 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15166086619) ^ 5055362206 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15166086619) ^ 322682694 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15166086619) ^ 282 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_16489485193 : Nat.Prime 16489485193 := by
  apply lucas_primality 16489485193 (7 : ZMod 16489485193)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (687061883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (687061883, 1)] : List FactorBlock).map factorBlockValue).prod) = 16489485193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_687061883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 16489485193) ^ 8244742596 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 16489485193) ^ 5496495064 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 16489485193) ^ 24 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_17478173717 : Nat.Prime 17478173717 := by
  apply lucas_primality 17478173717 (2 : ZMod 17478173717)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19417, 1), (225037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19417, 1), (225037, 1)] : List FactorBlock).map factorBlockValue).prod) = 17478173717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_19417
      · exact prime_thirteenK_225037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17478173717) ^ 8739086858 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17478173717) ^ 900148 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 17478173717) ^ 77668 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_18115486199 : Nat.Prime 18115486199 := by
  apply lucas_primality 18115486199 (13 : ZMod 18115486199)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (5701, 1), (83621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (5701, 1), (83621, 1)] : List FactorBlock).map factorBlockValue).prod) = 18115486199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_19
      · exact prime_thirteenK_5701
      · exact prime_thirteenK_83621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 18115486199) ^ 9057743099 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 18115486199) ^ 953446642 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 18115486199) ^ 3177598 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (13 : ZMod 18115486199) ^ 216638 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_19167809209 : Nat.Prime 19167809209 := by
  apply lucas_primality 19167809209 (7 : ZMod 19167809209)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3011, 1), (265247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3011, 1), (265247, 1)] : List FactorBlock).map factorBlockValue).prod) = 19167809209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_3011
      · exact prime_thirteenK_265247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 19167809209) ^ 9583904604 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 6389269736 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 6365928 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 19167809209) ^ 72264 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_19573338017 : Nat.Prime 19573338017 := by
  apply lucas_primality 19573338017 (3 : ZMod 19573338017)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (611666813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (611666813, 1)] : List FactorBlock).map factorBlockValue).prod) = 19573338017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_611666813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 19573338017) ^ 9786669008 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19573338017) ^ 32 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_19900204619 : Nat.Prime 19900204619 := by
  apply lucas_primality 19900204619 (2 : ZMod 19900204619)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4243, 1), (335009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4243, 1), (335009, 1)] : List FactorBlock).map factorBlockValue).prod) = 19900204619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_4243
      · exact prime_thirteenK_335009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19900204619) ^ 9950102309 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 2842886374 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 4690126 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 19900204619) ^ 59402 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_22801290529 : Nat.Prime 22801290529 := by
  apply lucas_primality 22801290529 (11 : ZMod 22801290529)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (61, 1), (233, 1), (983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (61, 1), (233, 1), (983, 1)] : List FactorBlock).map factorBlockValue).prod) = 22801290529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_17
      · exact prime_thirteenK_61
      · exact prime_thirteenK_233
      · exact prime_thirteenK_983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22801290529) ^ 11400645264 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22801290529) ^ 7600430176 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22801290529) ^ 1341252384 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22801290529) ^ 373791648 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22801290529) ^ 97859616 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22801290529) ^ 23195616 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_25822252091 : Nat.Prime 25822252091 := by
  apply lucas_primality 25822252091 (6 : ZMod 25822252091)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2582225209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2582225209, 1)] : List FactorBlock).map factorBlockValue).prod) = 25822252091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_2582225209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 25822252091) ^ 12911126045 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 25822252091) ^ 5164450418 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 25822252091) ^ 10 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_29486133581 : Nat.Prime 29486133581 := by
  apply lucas_primality 29486133581 (2 : ZMod 29486133581)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1474306679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1474306679, 1)] : List FactorBlock).map factorBlockValue).prod) = 29486133581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_1474306679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29486133581) ^ 14743066790 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29486133581) ^ 5897226716 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29486133581) ^ 20 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_36310173281 : Nat.Prime 36310173281 := by
  apply lucas_primality 36310173281 (3 : ZMod 36310173281)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (8641, 1), (26263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (8641, 1), (26263, 1)] : List FactorBlock).map factorBlockValue).prod) = 36310173281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_8641
      · exact prime_thirteenK_26263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 36310173281) ^ 18155086640 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 36310173281) ^ 7262034656 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 36310173281) ^ 4202080 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 36310173281) ^ 1382560 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_41162461121 : Nat.Prime 41162461121 := by
  apply lucas_primality 41162461121 (3 : ZMod 41162461121)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (11, 1), (101, 1), (115781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (11, 1), (101, 1), (115781, 1)] : List FactorBlock).map factorBlockValue).prod) = 41162461121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_11
      · exact prime_thirteenK_101
      · exact prime_thirteenK_115781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41162461121) ^ 20581230560 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41162461121) ^ 8232492224 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41162461121) ^ 3742041920 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41162461121) ^ 407549120 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41162461121) ^ 355520 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_44998184087 : Nat.Prime 44998184087 := by
  apply lucas_primality 44998184087 (5 : ZMod 44998184087)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (277, 1), (912631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (277, 1), (912631, 1)] : List FactorBlock).map factorBlockValue).prod) = 44998184087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_89
      · exact prime_thirteenK_277
      · exact prime_thirteenK_912631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44998184087) ^ 22499092043 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 44998184087) ^ 505597574 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 44998184087) ^ 162448318 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 44998184087) ^ 49306 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_57221363611 : Nat.Prime 57221363611 := by
  apply lucas_primality 57221363611 (2 : ZMod 57221363611)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (53, 1), (1697, 1), (7069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (53, 1), (1697, 1), (7069, 1)] : List FactorBlock).map factorBlockValue).prod) = 57221363611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_53
      · exact prime_thirteenK_1697
      · exact prime_thirteenK_7069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57221363611) ^ 28610681805 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 57221363611) ^ 19073787870 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 57221363611) ^ 11444272722 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 57221363611) ^ 1079648370 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 57221363611) ^ 33719130 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 57221363611) ^ 8094690 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_62027081687 : Nat.Prime 62027081687 := by
  apply lucas_primality 62027081687 (5 : ZMod 62027081687)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (244201109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (244201109, 1)] : List FactorBlock).map factorBlockValue).prod) = 62027081687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_127
      · exact prime_thirteenK_244201109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 62027081687) ^ 31013540843 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 62027081687) ^ 488402218 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 62027081687) ^ 254 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_72863556869 : Nat.Prime 72863556869 := by
  apply lucas_primality 72863556869 (2 : ZMod 72863556869)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (73, 1), (5309207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (73, 1), (5309207, 1)] : List FactorBlock).map factorBlockValue).prod) = 72863556869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_47
      · exact prime_thirteenK_73
      · exact prime_thirteenK_5309207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72863556869) ^ 36431778434 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 1550288444 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 998130916 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 72863556869) ^ 13724 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_104941231333 : Nat.Prime 104941231333 := by
  apply lucas_primality 104941231333 (2 : ZMod 104941231333)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (47, 1), (311, 1), (85469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (47, 1), (311, 1), (85469, 1)] : List FactorBlock).map factorBlockValue).prod) = 104941231333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_47
      · exact prime_thirteenK_311
      · exact prime_thirteenK_85469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104941231333) ^ 52470615666 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 34980410444 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 14991604476 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 2232792156 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 337431612 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104941231333) ^ 1227828 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_105842008711 : Nat.Prime 105842008711 := by
  apply lucas_primality 105842008711 (3 : ZMod 105842008711)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (31784387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (31784387, 1)] : List FactorBlock).map factorBlockValue).prod) = 105842008711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_37
      · exact prime_thirteenK_31784387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 105842008711) ^ 52921004355 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 105842008711) ^ 35280669570 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 105842008711) ^ 21168401742 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 105842008711) ^ 2860594830 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 105842008711) ^ 3330 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_212140652989 : Nat.Prime 212140652989 := by
  apply lucas_primality 212140652989 (2 : ZMod 212140652989)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (41, 1), (39198199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (41, 1), (39198199, 1)] : List FactorBlock).map factorBlockValue).prod) = 212140652989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_41
      · exact prime_thirteenK_39198199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212140652989) ^ 106070326494 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 70713550996 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 19285513908 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 5174162268 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 212140652989) ^ 5412 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_213502379527 : Nat.Prime 213502379527 := by
  apply lucas_primality 213502379527 (3 : ZMod 213502379527)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1317915923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1317915923, 1)] : List FactorBlock).map factorBlockValue).prod) = 213502379527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_1317915923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 213502379527) ^ 106751189763 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 213502379527) ^ 71167459842 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 213502379527) ^ 162 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_240255168799 : Nat.Prime 240255168799 := by
  apply lucas_primality 240255168799 (3 : ZMod 240255168799)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (617, 1), (64898749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (617, 1), (64898749, 1)] : List FactorBlock).map factorBlockValue).prod) = 240255168799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_617
      · exact prime_thirteenK_64898749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 240255168799) ^ 120127584399 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 240255168799) ^ 80085056266 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 240255168799) ^ 389392494 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 240255168799) ^ 3702 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_272119617229 : Nat.Prime 272119617229 := by
  apply lucas_primality 272119617229 (2 : ZMod 272119617229)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3463, 1), (6548263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3463, 1), (6548263, 1)] : List FactorBlock).map factorBlockValue).prod) = 272119617229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_3463
      · exact prime_thirteenK_6548263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 272119617229) ^ 136059808614 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 272119617229) ^ 90706539076 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 272119617229) ^ 78579156 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 272119617229) ^ 41556 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_318960960511 : Nat.Prime 318960960511 := by
  apply lucas_primality 318960960511 (17 : ZMod 318960960511)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9719, 1), (1093943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9719, 1), (1093943, 1)] : List FactorBlock).map factorBlockValue).prod) = 318960960511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_9719
      · exact prime_thirteenK_1093943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 318960960511) ^ 159480480255 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 106320320170 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 63792192102 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 32818290 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 318960960511) ^ 291570 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_329299688969 : Nat.Prime 329299688969 := by
  apply lucas_primality 329299688969 (3 : ZMod 329299688969)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41162461121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41162461121, 1)] : List FactorBlock).map factorBlockValue).prod) = 329299688969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_41162461121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 329299688969) ^ 164649844484 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 329299688969) ^ 8 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_375380267527 : Nat.Prime 375380267527 := by
  apply lucas_primality 375380267527 (5 : ZMod 375380267527)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (127, 1), (157, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (127, 1), (157, 1), (95083, 1)] : List FactorBlock).map factorBlockValue).prod) = 375380267527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_127
      · exact prime_thirteenK_157
      · exact prime_thirteenK_95083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 375380267527) ^ 187690133763 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 125126755842 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 34125478866 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 2955750138 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 2390957118 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 375380267527) ^ 3947922 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_435766473283 : Nat.Prime 435766473283 := by
  apply lucas_primality 435766473283 (2 : ZMod 435766473283)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2617, 1), (3964613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2617, 1), (3964613, 1)] : List FactorBlock).map factorBlockValue).prod) = 435766473283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_2617
      · exact prime_thirteenK_3964613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 435766473283) ^ 217883236641 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 435766473283) ^ 145255491094 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 435766473283) ^ 62252353326 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 435766473283) ^ 166513746 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 435766473283) ^ 109914 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_17
      · exact prime_thirteenK_397
      · exact prime_thirteenK_2531
      · exact prime_thirteenK_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_548528279441 : Nat.Prime 548528279441 := by
  apply lucas_primality 548528279441 (3 : ZMod 548528279441)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (6856603493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (6856603493, 1)] : List FactorBlock).map factorBlockValue).prod) = 548528279441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_6856603493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 548528279441) ^ 274264139720 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 548528279441) ^ 109705655888 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 548528279441) ^ 80 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_580594587409 : Nat.Prime 580594587409 := by
  apply lucas_primality 580594587409 (19 : ZMod 580594587409)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (11, 1), (6563, 1), (55849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (11, 1), (6563, 1), (55849, 1)] : List FactorBlock).map factorBlockValue).prod) = 580594587409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_6563
      · exact prime_thirteenK_55849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 580594587409) ^ 290297293704 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (19 : ZMod 580594587409) ^ 193531529136 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (19 : ZMod 580594587409) ^ 52781326128 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (19 : ZMod 580594587409) ^ 88464816 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (19 : ZMod 580594587409) ^ 10395792 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_590282327407 : Nat.Prime 590282327407 := by
  apply lucas_primality 590282327407 (3 : ZMod 590282327407)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (34361, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) = 590282327407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_29
      · exact prime_thirteenK_34361
      · exact prime_thirteenK_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 590282327407) ^ 295141163703 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 196760775802 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 20354563014 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 17178846 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 590282327407) ^ 5978814 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_871794576241 : Nat.Prime 871794576241 := by
  apply lucas_primality 871794576241 (29 : ZMod 871794576241)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (518925343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (518925343, 1)] : List FactorBlock).map factorBlockValue).prod) = 871794576241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_518925343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 871794576241) ^ 435897288120 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (29 : ZMod 871794576241) ^ 290598192080 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (29 : ZMod 871794576241) ^ 174358915248 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (29 : ZMod 871794576241) ^ 124542082320 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (29 : ZMod 871794576241) ^ 1680 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_906007626637 : Nat.Prime 906007626637 := by
  apply lucas_primality 906007626637 (2 : ZMod 906007626637)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 3), (220118471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 3), (220118471, 1)] : List FactorBlock).map factorBlockValue).prod) = 906007626637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_220118471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906007626637) ^ 453003813318 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 302002542212 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 129429660948 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 906007626637) ^ 4116 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_951075532889 : Nat.Prime 951075532889 := by
  apply lucas_primality 951075532889 (3 : ZMod 951075532889)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (9144957047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (9144957047, 1)] : List FactorBlock).map factorBlockValue).prod) = 951075532889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_9144957047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 951075532889) ^ 475537766444 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 951075532889) ^ 73159656376 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 951075532889) ^ 104 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1091817788989 : Nat.Prime 1091817788989 := by
  apply lucas_primality 1091817788989 (2 : ZMod 1091817788989)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20719, 1), (4391371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20719, 1), (4391371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1091817788989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_20719
      · exact prime_thirteenK_4391371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1091817788989) ^ 545908894494 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091817788989) ^ 363939262996 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091817788989) ^ 52696452 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1091817788989) ^ 248628 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1123160144339 : Nat.Prime 1123160144339 := by
  apply lucas_primality 1123160144339 (2 : ZMod 1123160144339)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (18115486199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (18115486199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1123160144339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_31
      · exact prime_thirteenK_18115486199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1123160144339) ^ 561580072169 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123160144339) ^ 36230972398 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123160144339) ^ 62 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1237167199903 : Nat.Prime 1237167199903 := by
  apply lucas_primality 1237167199903 (3 : ZMod 1237167199903)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (307, 1), (671643431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (307, 1), (671643431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1237167199903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_307
      · exact prime_thirteenK_671643431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1237167199903) ^ 618583599951 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1237167199903) ^ 412389066634 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1237167199903) ^ 4029860586 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1237167199903) ^ 1842 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_35279
      · exact prime_thirteenK_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1605680900297 : Nat.Prime 1605680900297 := by
  apply lucas_primality 1605680900297 (3 : ZMod 1605680900297)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (101, 1), (907, 1), (199181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (101, 1), (907, 1), (199181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1605680900297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_11
      · exact prime_thirteenK_101
      · exact prime_thirteenK_907
      · exact prime_thirteenK_199181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1605680900297) ^ 802840450148 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1605680900297) ^ 145970990936 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1605680900297) ^ 15897830696 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1605680900297) ^ 1770320728 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1605680900297) ^ 8061416 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2903228044637 : Nat.Prime 2903228044637 := by
  apply lucas_primality 2903228044637 (2 : ZMod 2903228044637)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (37, 1), (79, 1), (8562377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (37, 1), (79, 1), (8562377, 1)] : List FactorBlock).map factorBlockValue).prod) = 2903228044637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_29
      · exact prime_thirteenK_37
      · exact prime_thirteenK_79
      · exact prime_thirteenK_8562377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2903228044637) ^ 1451614022318 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2903228044637) ^ 100111311884 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2903228044637) ^ 78465622828 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2903228044637) ^ 36749722084 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2903228044637) ^ 339068 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_3272997965299 : Nat.Prime 3272997965299 := by
  apply lucas_primality 3272997965299 (2 : ZMod 3272997965299)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (719, 1), (758692157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (719, 1), (758692157, 1)] : List FactorBlock).map factorBlockValue).prod) = 3272997965299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_719
      · exact prime_thirteenK_758692157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3272997965299) ^ 1636498982649 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 1090999321766 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 4552152942 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3272997965299) ^ 4314 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_4266263672987 : Nat.Prime 4266263672987 := by
  apply lucas_primality 4266263672987 (2 : ZMod 4266263672987)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (101, 1), (97327729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (101, 1), (97327729, 1)] : List FactorBlock).map factorBlockValue).prod) = 4266263672987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_31
      · exact prime_thirteenK_101
      · exact prime_thirteenK_97327729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4266263672987) ^ 2133131836493 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4266263672987) ^ 609466238998 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4266263672987) ^ 137621408806 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4266263672987) ^ 42240234386 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4266263672987) ^ 43834 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_4802648953049 : Nat.Prime 4802648953049 := by
  apply lucas_primality 4802648953049 (3 : ZMod 4802648953049)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (43, 1), (821246401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (43, 1), (821246401, 1)] : List FactorBlock).map factorBlockValue).prod) = 4802648953049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_17
      · exact prime_thirteenK_43
      · exact prime_thirteenK_821246401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4802648953049) ^ 2401324476524 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4802648953049) ^ 282508761944 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4802648953049) ^ 111689510536 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4802648953049) ^ 5848 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_5452977238001 : Nat.Prime 5452977238001 := by
  apply lucas_primality 5452977238001 (3 : ZMod 5452977238001)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (19, 1), (3877, 1), (37013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (19, 1), (3877, 1), (37013, 1)] : List FactorBlock).map factorBlockValue).prod) = 5452977238001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_19
      · exact prime_thirteenK_3877
      · exact prime_thirteenK_37013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5452977238001) ^ 2726488619000 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 1090595447600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 286998802000 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 1406494000 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5452977238001) ^ 147326000 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_5457459350351 : Nat.Prime 5457459350351 := by
  apply lucas_primality 5457459350351 (7 : ZMod 5457459350351)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (19, 1), (419, 1), (1958641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (19, 1), (419, 1), (1958641, 1)] : List FactorBlock).map factorBlockValue).prod) = 5457459350351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_19
      · exact prime_thirteenK_419
      · exact prime_thirteenK_1958641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5457459350351) ^ 2728729675175 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5457459350351) ^ 1091491870070 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5457459350351) ^ 779637050050 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5457459350351) ^ 287234702650 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5457459350351) ^ 13024962650 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5457459350351) ^ 2786350 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_5493250906657 : Nat.Prime 5493250906657 := by
  apply lucas_primality 5493250906657 (5 : ZMod 5493250906657)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (57221363611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (57221363611, 1)] : List FactorBlock).map factorBlockValue).prod) = 5493250906657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_57221363611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5493250906657) ^ 2746625453328 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 5493250906657) ^ 1831083635552 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 5493250906657) ^ 96 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_6523728322439 : Nat.Prime 6523728322439 := by
  apply lucas_primality 6523728322439 (11 : ZMod 6523728322439)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (3191, 1), (17325551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (3191, 1), (17325551, 1)] : List FactorBlock).map factorBlockValue).prod) = 6523728322439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_59
      · exact prime_thirteenK_3191
      · exact prime_thirteenK_17325551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6523728322439) ^ 3261864161219 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 6523728322439) ^ 110571666482 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 6523728322439) ^ 2044415018 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 6523728322439) ^ 376538 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_7061169065849 : Nat.Prime 7061169065849 := by
  apply lucas_primality 7061169065849 (3 : ZMod 7061169065849)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (127, 1), (733, 1), (178897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (127, 1), (733, 1), (178897, 1)] : List FactorBlock).map factorBlockValue).prod) = 7061169065849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_53
      · exact prime_thirteenK_127
      · exact prime_thirteenK_733
      · exact prime_thirteenK_178897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7061169065849) ^ 3530584532924 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 7061169065849) ^ 133229605016 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 7061169065849) ^ 55599756424 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 7061169065849) ^ 9633245656 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 7061169065849) ^ 39470584 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_11888851128907 : Nat.Prime 11888851128907 := by
  apply lucas_primality 11888851128907 (3 : ZMod 11888851128907)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (3041, 1), (318313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (3041, 1), (318313, 1)] : List FactorBlock).map factorBlockValue).prod) = 11888851128907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_23
      · exact prime_thirteenK_89
      · exact prime_thirteenK_3041
      · exact prime_thirteenK_318313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11888851128907) ^ 5944425564453 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 3962950376302 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 516906570822 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 133582596954 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 3909520266 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 11888851128907) ^ 37349562 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_24705200084659 : Nat.Prime 24705200084659 := by
  apply lucas_primality 24705200084659 (2 : ZMod 24705200084659)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229, 1), (12569, 1), (1430543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229, 1), (12569, 1), (1430543, 1)] : List FactorBlock).map factorBlockValue).prod) = 24705200084659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_229
      · exact prime_thirteenK_12569
      · exact prime_thirteenK_1430543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24705200084659) ^ 12352600042329 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 8235066694886 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 107882969802 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 1965566082 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24705200084659) ^ 17269806 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_25692720254657 : Nat.Prime 25692720254657 := by
  apply lucas_primality 25692720254657 (5 : ZMod 25692720254657)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (13, 1), (17, 1), (499, 1), (520043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (13, 1), (17, 1), (499, 1), (520043, 1)] : List FactorBlock).map factorBlockValue).prod) = 25692720254657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_499
      · exact prime_thirteenK_520043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25692720254657) ^ 12846360127328 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25692720254657) ^ 3670388607808 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25692720254657) ^ 1976363096512 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25692720254657) ^ 1511336485568 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25692720254657) ^ 51488417344 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 25692720254657) ^ 49404992 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_27152987060723 : Nat.Prime 27152987060723 := by
  apply lucas_primality 27152987060723 (2 : ZMod 27152987060723)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (590282327407, 1)] : List FactorBlock).map factorBlockValue).prod) = 27152987060723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_23
      · exact prime_thirteenK_590282327407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27152987060723) ^ 13576493530361 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 1180564654814 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27152987060723) ^ 46 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_28322570842457 : Nat.Prime 28322570842457 := by
  apply lucas_primality 28322570842457 (5 : ZMod 28322570842457)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (17, 1), (5569, 1), (3399569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (17, 1), (5569, 1), (3399569, 1)] : List FactorBlock).map factorBlockValue).prod) = 28322570842457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_11
      · exact prime_thirteenK_17
      · exact prime_thirteenK_5569
      · exact prime_thirteenK_3399569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 28322570842457) ^ 14161285421228 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 2574779167496 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 1666033578968 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 5085755224 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 28322570842457) ^ 8331224 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_33335486753399 : Nat.Prime 33335486753399 := by
  apply lucas_primality 33335486753399 (29 : ZMod 33335486753399)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (43, 1), (22801290529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (43, 1), (22801290529, 1)] : List FactorBlock).map factorBlockValue).prod) = 33335486753399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_17
      · exact prime_thirteenK_43
      · exact prime_thirteenK_22801290529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 33335486753399) ^ 16667743376699 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (29 : ZMod 33335486753399) ^ 1960910985494 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (29 : ZMod 33335486753399) ^ 775243877986 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (29 : ZMod 33335486753399) ^ 1462 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_50456514775123 : Nat.Prime 50456514775123 := by
  apply lucas_primality 50456514775123 (2 : ZMod 50456514775123)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2593, 1), (360347051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2593, 1), (360347051, 1)] : List FactorBlock).map factorBlockValue).prod) = 50456514775123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_2593
      · exact prime_thirteenK_360347051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50456514775123) ^ 25228257387561 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 16818838258374 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 19458740754 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 50456514775123) ^ 140022 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_65398790854597 : Nat.Prime 65398790854597 := by
  apply lucas_primality 65398790854597 (5 : ZMod 65398790854597)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (83, 1), (151, 1), (14994619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (83, 1), (151, 1), (14994619, 1)] : List FactorBlock).map factorBlockValue).prod) = 65398790854597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_29
      · exact prime_thirteenK_83
      · exact prime_thirteenK_151
      · exact prime_thirteenK_14994619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 65398790854597) ^ 32699395427298 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 65398790854597) ^ 21799596951532 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 65398790854597) ^ 2255130719124 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 65398790854597) ^ 787937239212 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 65398790854597) ^ 433104575196 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 65398790854597) ^ 4361484 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_82409921292943 : Nat.Prime 82409921292943 := by
  apply lucas_primality 82409921292943 (3 : ZMod 82409921292943)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (71, 1), (331, 1), (64938073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (71, 1), (331, 1), (64938073, 1)] : List FactorBlock).map factorBlockValue).prod) = 82409921292943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_71
      · exact prime_thirteenK_331
      · exact prime_thirteenK_64938073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 82409921292943) ^ 41204960646471 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82409921292943) ^ 27469973764314 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82409921292943) ^ 1160703116802 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82409921292943) ^ 248972571882 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 82409921292943) ^ 1269054 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_102102247358591 : Nat.Prime 102102247358591 := by
  apply lucas_primality 102102247358591 (14 : ZMod 102102247358591)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (523, 1), (10159, 1), (1921687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (523, 1), (10159, 1), (1921687, 1)] : List FactorBlock).map factorBlockValue).prod) = 102102247358591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_523
      · exact prime_thirteenK_10159
      · exact prime_thirteenK_1921687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 102102247358591) ^ 51051123679295 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 20420449471718 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 195224182330 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 10050423010 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 102102247358591) ^ 53131570 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_119134327776067 : Nat.Prime 119134327776067 := by
  apply lucas_primality 119134327776067 (7 : ZMod 119134327776067)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (213502379527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (213502379527, 1)] : List FactorBlock).map factorBlockValue).prod) = 119134327776067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_31
      · exact prime_thirteenK_213502379527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 119134327776067) ^ 59567163888033 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 39711442592022 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 3843042831486 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 119134327776067) ^ 558 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_120413239471199 : Nat.Prime 120413239471199 := by
  apply lucas_primality 120413239471199 (11 : ZMod 120413239471199)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (923579, 1), (2102851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (923579, 1), (2102851, 1)] : List FactorBlock).map factorBlockValue).prod) = 120413239471199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_31
      · exact prime_thirteenK_923579
      · exact prime_thirteenK_2102851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 120413239471199) ^ 60206619735599 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 120413239471199) ^ 3884298047458 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 120413239471199) ^ 130376762 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 120413239471199) ^ 57261898 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_160284903568781 : Nat.Prime 160284903568781 := by
  apply lucas_primality 160284903568781 (2 : ZMod 160284903568781)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (61, 1), (113, 1), (68392019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (61, 1), (113, 1), (68392019, 1)] : List FactorBlock).map factorBlockValue).prod) = 160284903568781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_17
      · exact prime_thirteenK_61
      · exact prime_thirteenK_113
      · exact prime_thirteenK_68392019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 160284903568781) ^ 80142451784390 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 32056980713756 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 9428523739340 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 2627621369980 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 1418450474060 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160284903568781) ^ 2343620 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_186500232644353 : Nat.Prime 186500232644353 := by
  apply lucas_primality 186500232644353 (14 : ZMod 186500232644353)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (11, 1), (17, 1), (67, 1), (19382141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (11, 1), (17, 1), (67, 1), (19382141, 1)] : List FactorBlock).map factorBlockValue).prod) = 186500232644353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_17
      · exact prime_thirteenK_67
      · exact prime_thirteenK_19382141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 186500232644353) ^ 93250116322176 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186500232644353) ^ 62166744214784 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186500232644353) ^ 16954566604032 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186500232644353) ^ 10970601920256 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186500232644353) ^ 2783585561856 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 186500232644353) ^ 9622272 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_200372810778367 : Nat.Prime 200372810778367 := by
  apply lucas_primality 200372810778367 (3 : ZMod 200372810778367)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (240255168799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (240255168799, 1)] : List FactorBlock).map factorBlockValue).prod) = 200372810778367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_139
      · exact prime_thirteenK_240255168799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 200372810778367) ^ 100186405389183 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 200372810778367) ^ 66790936926122 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 200372810778367) ^ 1441531012794 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 200372810778367) ^ 834 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_226043412291283 : Nat.Prime 226043412291283 := by
  apply lucas_primality 226043412291283 (2 : ZMod 226043412291283)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (104941231333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (104941231333, 1)] : List FactorBlock).map factorBlockValue).prod) = 226043412291283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_359
      · exact prime_thirteenK_104941231333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 226043412291283) ^ 113021706145641 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 75347804097094 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 629647387998 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 226043412291283) ^ 2154 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_304128603975499 : Nat.Prime 304128603975499 := by
  apply lucas_primality 304128603975499 (3 : ZMod 304128603975499)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (3109, 1), (158288029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (3109, 1), (158288029, 1)] : List FactorBlock).map factorBlockValue).prod) = 304128603975499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_103
      · exact prime_thirteenK_3109
      · exact prime_thirteenK_158288029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 304128603975499) ^ 152064301987749 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 101376201325166 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 2952704892966 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 97822001922 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 304128603975499) ^ 1921362 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_366444555641737 : Nat.Prime 366444555641737 := by
  apply lucas_primality 366444555641737 (5 : ZMod 366444555641737)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (487, 1), (1381, 1), (158759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (487, 1), (1381, 1), (158759, 1)] : List FactorBlock).map factorBlockValue).prod) = 366444555641737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_487
      · exact prime_thirteenK_1381
      · exact prime_thirteenK_158759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 366444555641737) ^ 183222277820868 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 122148185213912 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 33313141421976 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 28188042741672 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 752452886328 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 265347252456 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 366444555641737) ^ 2308181304 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_456818736397697 : Nat.Prime 456818736397697 := by
  apply lucas_primality 456818736397697 (3 : ZMod 456818736397697)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (67, 1), (28807, 1), (1849103, 1)] : List FactorBlock).map factorBlockValue).prod) = 456818736397697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_67
      · exact prime_thirteenK_28807
      · exact prime_thirteenK_1849103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 456818736397697) ^ 228409368198848 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 6818190095488 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 15857907328 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 456818736397697) ^ 247048832 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_504370657970869 : Nat.Prime 504370657970869 := by
  apply lucas_primality 504370657970869 (2 : ZMod 504370657970869)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (79, 1), (109, 1), (11159, 1), (33647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (79, 1), (109, 1), (11159, 1), (33647, 1)] : List FactorBlock).map factorBlockValue).prod) = 504370657970869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_79
      · exact prime_thirteenK_109
      · exact prime_thirteenK_11159
      · exact prime_thirteenK_33647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 504370657970869) ^ 252185328985434 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 504370657970869) ^ 168123552656956 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 504370657970869) ^ 38797742920836 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 504370657970869) ^ 6384438708492 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 504370657970869) ^ 4627253742852 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 504370657970869) ^ 45198553452 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 504370657970869) ^ 14990063244 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_652951539706483 : Nat.Prime 652951539706483 := by
  apply lucas_primality 652951539706483 (3 : ZMod 652951539706483)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (11353, 1), (86356709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (11353, 1), (86356709, 1)] : List FactorBlock).map factorBlockValue).prod) = 652951539706483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_37
      · exact prime_thirteenK_11353
      · exact prime_thirteenK_86356709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 652951539706483) ^ 326475769853241 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 652951539706483) ^ 217650513235494 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 652951539706483) ^ 17647338910986 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 652951539706483) ^ 57513568194 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 652951539706483) ^ 7561098 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1091318243936369 : Nat.Prime 1091318243936369 := by
  apply lucas_primality 1091318243936369 (3 : ZMod 1091318243936369)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (31, 1), (59, 1), (5327453741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (31, 1), (59, 1), (5327453741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1091318243936369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_31
      · exact prime_thirteenK_59
      · exact prime_thirteenK_5327453741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1091318243936369) ^ 545659121968184 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 155902606276624 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 35203814320528 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 18496919388752 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1091318243936369) ^ 204848 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1159057776105457 : Nat.Prime 1159057776105457 := by
  apply lucas_primality 1159057776105457 (5 : ZMod 1159057776105457)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (37, 1), (71, 1), (257, 1), (1009, 1), (35447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (37, 1), (71, 1), (257, 1), (1009, 1), (35447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1159057776105457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_37
      · exact prime_thirteenK_71
      · exact prime_thirteenK_257
      · exact prime_thirteenK_1009
      · exact prime_thirteenK_35447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1159057776105457) ^ 579528888052728 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 386352592035152 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 31325885840688 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 16324757409936 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 4509952436208 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 1148719302384 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1159057776105457) ^ 32698332048 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1318012956300611 : Nat.Prime 1318012956300611 := by
  apply lucas_primality 1318012956300611 (6 : ZMod 1318012956300611)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (977, 1), (11503, 1), (617249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (977, 1), (11503, 1), (617249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1318012956300611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_19
      · exact prime_thirteenK_977
      · exact prime_thirteenK_11503
      · exact prime_thirteenK_617249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1318012956300611) ^ 659006478150305 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1318012956300611) ^ 263602591260122 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1318012956300611) ^ 69369102963190 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1318012956300611) ^ 1349040896930 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1318012956300611) ^ 114579931870 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1318012956300611) ^ 2135301890 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1337890974223129 : Nat.Prime 1337890974223129 := by
  apply lucas_primality 1337890974223129 (11 : ZMod 1337890974223129)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (37, 1), (2917, 1), (39730861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (37, 1), (2917, 1), (39730861, 1)] : List FactorBlock).map factorBlockValue).prod) = 1337890974223129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_37
      · exact prime_thirteenK_2917
      · exact prime_thirteenK_39730861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1337890974223129) ^ 668945487111564 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1337890974223129) ^ 445963658074376 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1337890974223129) ^ 102914690324856 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1337890974223129) ^ 36159215519544 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1337890974223129) ^ 458653059384 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1337890974223129) ^ 33673848 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1439247440577409 : Nat.Prime 1439247440577409 := by
  apply lucas_primality 1439247440577409 (17 : ZMod 1439247440577409)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (11, 1), (547, 1), (88986923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (11, 1), (547, 1), (88986923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1439247440577409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_547
      · exact prime_thirteenK_88986923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1439247440577409) ^ 719623720288704 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1439247440577409) ^ 479749146859136 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1439247440577409) ^ 205606777225344 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1439247440577409) ^ 130840676416128 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1439247440577409) ^ 2631165339264 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (17 : ZMod 1439247440577409) ^ 16173696 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_11
      · exact prime_thirteenK_41
      · exact prime_thirteenK_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2533801651658729 : Nat.Prime 2533801651658729 := by
  apply lucas_primality 2533801651658729 (3 : ZMod 2533801651658729)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (67, 1), (101, 1), (157, 1), (27101549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (67, 1), (101, 1), (157, 1), (27101549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2533801651658729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_11
      · exact prime_thirteenK_67
      · exact prime_thirteenK_101
      · exact prime_thirteenK_157
      · exact prime_thirteenK_27101549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2533801651658729) ^ 1266900825829364 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2533801651658729) ^ 230345604696248 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2533801651658729) ^ 37817935099384 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2533801651658729) ^ 25087145065928 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2533801651658729) ^ 16138864023304 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2533801651658729) ^ 93492872 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2636025912601223 : Nat.Prime 2636025912601223 := by
  apply lucas_primality 2636025912601223 (5 : ZMod 2636025912601223)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1318012956300611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1318012956300611, 1)] : List FactorBlock).map factorBlockValue).prod) = 2636025912601223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_1318012956300611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2636025912601223) ^ 1318012956300611 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2636025912601223) ^ 2 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_3080389673224709 : Nat.Prime 3080389673224709 := by
  apply lucas_primality 3080389673224709 (2 : ZMod 3080389673224709)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (967, 1), (28229, 1), (166931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (967, 1), (28229, 1), (166931, 1)] : List FactorBlock).map factorBlockValue).prod) = 3080389673224709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_967
      · exact prime_thirteenK_28229
      · exact prime_thirteenK_166931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3080389673224709) ^ 1540194836612354 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 236953051786516 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 3185511554524 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 109121459252 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3080389673224709) ^ 18453071468 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_3300259784395591 : Nat.Prime 3300259784395591 := by
  apply lucas_primality 3300259784395591 (3 : ZMod 3300259784395591)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (75557, 1), (13116839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (75557, 1), (13116839, 1)] : List FactorBlock).map factorBlockValue).prod) = 3300259784395591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_37
      · exact prime_thirteenK_75557
      · exact prime_thirteenK_13116839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3300259784395591) ^ 1650129892197795 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 1100086594798530 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 660051956879118 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 89196210389070 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 43679073870 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3300259784395591) ^ 251604810 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_3750138237419351 : Nat.Prime 3750138237419351 := by
  apply lucas_primality 3750138237419351 (7 : ZMod 3750138237419351)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (29, 1), (401, 1), (619, 1), (64717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (29, 1), (401, 1), (619, 1), (64717, 1)] : List FactorBlock).map factorBlockValue).prod) = 3750138237419351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_401
      · exact prime_thirteenK_619
      · exact prime_thirteenK_64717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3750138237419351) ^ 1875069118709675 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3750138237419351) ^ 750027647483870 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3750138237419351) ^ 535734033917050 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3750138237419351) ^ 163049488583450 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3750138237419351) ^ 129315111635150 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3750138237419351) ^ 9351965679350 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3750138237419351) ^ 6058381643650 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3750138237419351) ^ 57946725550 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_4261734374713931 : Nat.Prime 4261734374713931 := by
  apply lucas_primality 4261734374713931 (2 : ZMod 4261734374713931)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (61, 1), (83, 1), (4430215469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (61, 1), (83, 1), (4430215469, 1)] : List FactorBlock).map factorBlockValue).prod) = 4261734374713931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_19
      · exact prime_thirteenK_61
      · exact prime_thirteenK_83
      · exact prime_thirteenK_4430215469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4261734374713931) ^ 2130867187356965 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4261734374713931) ^ 852346874942786 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4261734374713931) ^ 224301809195470 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4261734374713931) ^ 69864497946130 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4261734374713931) ^ 51346197285710 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4261734374713931) ^ 961970 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_5664798049611737 : Nat.Prime 5664798049611737 := by
  apply lucas_primality 5664798049611737 (3 : ZMod 5664798049611737)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (227873, 1), (63416971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (227873, 1), (63416971, 1)] : List FactorBlock).map factorBlockValue).prod) = 5664798049611737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_227873
      · exact prime_thirteenK_63416971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5664798049611737) ^ 2832399024805868 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5664798049611737) ^ 809256864230248 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5664798049611737) ^ 24859452632 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5664798049611737) ^ 89326216 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_5736548500147109 : Nat.Prime 5736548500147109 := by
  apply lucas_primality 5736548500147109 (2 : ZMod 5736548500147109)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (157, 1), (44998184087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (157, 1), (44998184087, 1)] : List FactorBlock).map factorBlockValue).prod) = 5736548500147109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_29
      · exact prime_thirteenK_157
      · exact prime_thirteenK_44998184087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5736548500147109) ^ 2868274250073554 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5736548500147109) ^ 819506928592444 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5736548500147109) ^ 197812017246452 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5736548500147109) ^ 36538525478644 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5736548500147109) ^ 127484 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_6395462309567759 : Nat.Prime 6395462309567759 := by
  apply lucas_primality 6395462309567759 (7 : ZMod 6395462309567759)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (456818736397697, 1)] : List FactorBlock).map factorBlockValue).prod) = 6395462309567759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_456818736397697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6395462309567759) ^ 3197731154783879 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 913637472795394 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6395462309567759) ^ 14 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_6904261896540637 : Nat.Prime 6904261896540637 := by
  apply lucas_primality 6904261896540637 (6 : ZMod 6904261896540637)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (240509, 1), (2392239617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (240509, 1), (2392239617, 1)] : List FactorBlock).map factorBlockValue).prod) = 6904261896540637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_240509
      · exact prime_thirteenK_2392239617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6904261896540637) ^ 3452130948270318 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6904261896540637) ^ 2301420632180212 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6904261896540637) ^ 28706875404 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6904261896540637) ^ 2886108 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_7500276474838703 : Nat.Prime 7500276474838703 := by
  apply lucas_primality 7500276474838703 (5 : ZMod 7500276474838703)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3750138237419351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3750138237419351, 1)] : List FactorBlock).map factorBlockValue).prod) = 7500276474838703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3750138237419351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 7500276474838703) ^ 3750138237419351 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 7500276474838703) ^ 2 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_11895479753831941 : Nat.Prime 11895479753831941 := by
  apply lucas_primality 11895479753831941 (2 : ZMod 11895479753831941)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (28322570842457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (28322570842457, 1)] : List FactorBlock).map factorBlockValue).prod) = 11895479753831941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_28322570842457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11895479753831941) ^ 5947739876915970 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 3965159917943980 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 2379095950766388 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 1699354250547420 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11895479753831941) ^ 420 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_12104895791300857 : Nat.Prime 12104895791300857 := by
  apply lucas_primality 12104895791300857 (5 : ZMod 12104895791300857)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (504370657970869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (504370657970869, 1)] : List FactorBlock).map factorBlockValue).prod) = 12104895791300857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_504370657970869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12104895791300857) ^ 6052447895650428 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 12104895791300857) ^ 4034965263766952 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 12104895791300857) ^ 24 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_14211369920432687 : Nat.Prime 14211369920432687 := by
  apply lucas_primality 14211369920432687 (5 : ZMod 14211369920432687)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14989397, 1), (474047419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14989397, 1), (474047419, 1)] : List FactorBlock).map factorBlockValue).prod) = 14211369920432687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_14989397
      · exact prime_thirteenK_474047419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 14211369920432687) ^ 7105684960216343 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 14211369920432687) ^ 948094838 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 14211369920432687) ^ 29978794 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_19236651994427557 : Nat.Prime 19236651994427557 := by
  apply lucas_primality 19236651994427557 (6 : ZMod 19236651994427557)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1511, 1), (284803, 1), (286547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1511, 1), (284803, 1), (286547, 1)] : List FactorBlock).map factorBlockValue).prod) = 19236651994427557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_13
      · exact prime_thirteenK_1511
      · exact prime_thirteenK_284803
      · exact prime_thirteenK_286547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19236651994427557) ^ 9618325997213778 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 19236651994427557) ^ 6412217331475852 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 19236651994427557) ^ 1479742461109812 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 19236651994427557) ^ 12731073457596 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 19236651994427557) ^ 67543712652 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 19236651994427557) ^ 67132623948 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_25024350819790243 : Nat.Prime 25024350819790243 := by
  apply lucas_primality 25024350819790243 (2 : ZMod 25024350819790243)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47149, 1), (29486133581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47149, 1), (29486133581, 1)] : List FactorBlock).map factorBlockValue).prod) = 25024350819790243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_47149
      · exact prime_thirteenK_29486133581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25024350819790243) ^ 12512175409895121 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 8341450273263414 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 530750404458 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 25024350819790243) ^ 848682 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_27793292736046007 : Nat.Prime 27793292736046007 := by
  apply lucas_primality 27793292736046007 (5 : ZMod 27793292736046007)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (61, 1), (257, 1), (7219, 1), (9445537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (61, 1), (257, 1), (7219, 1), (9445537, 1)] : List FactorBlock).map factorBlockValue).prod) = 27793292736046007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_61
      · exact prime_thirteenK_257
      · exact prime_thirteenK_7219
      · exact prime_thirteenK_9445537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 27793292736046007) ^ 13896646368023003 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 2137945595080462 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 455627749771246 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 108145107922358 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 3850019772274 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 27793292736046007) ^ 2942478838 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_29464415336911963 : Nat.Prime 29464415336911963 := by
  apply lucas_primality 29464415336911963 (2 : ZMod 29464415336911963)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (1195031, 1), (8687729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (1195031, 1), (8687729, 1)] : List FactorBlock).map factorBlockValue).prod) = 29464415336911963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_43
      · exact prime_thirteenK_1195031
      · exact prime_thirteenK_8687729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29464415336911963) ^ 14732207668455981 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29464415336911963) ^ 9821471778970654 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29464415336911963) ^ 2678583212446542 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29464415336911963) ^ 685218961323534 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29464415336911963) ^ 24655774902 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29464415336911963) ^ 3391497978 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_30133561870930829 : Nat.Prime 30133561870930829 := by
  apply lucas_primality 30133561870930829 (2 : ZMod 30133561870930829)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (160284903568781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (160284903568781, 1)] : List FactorBlock).map factorBlockValue).prod) = 30133561870930829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_47
      · exact prime_thirteenK_160284903568781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30133561870930829) ^ 15066780935465414 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30133561870930829) ^ 641139614275124 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30133561870930829) ^ 188 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_112396776185790097 : Nat.Prime 112396776185790097 := by
  apply lucas_primality 112396776185790097 (5 : ZMod 112396776185790097)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (11, 1), (13, 1), (1531, 1), (1527929617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (11, 1), (13, 1), (1531, 1), (1527929617, 1)] : List FactorBlock).map factorBlockValue).prod) = 112396776185790097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_1531
      · exact prime_thirteenK_1527929617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 112396776185790097) ^ 56198388092895048 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112396776185790097) ^ 37465592061930032 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112396776185790097) ^ 16056682312255728 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112396776185790097) ^ 10217888744162736 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112396776185790097) ^ 8645905860445392 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112396776185790097) ^ 73413962237616 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 112396776185790097) ^ 73561488 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_146803238938895719 : Nat.Prime 146803238938895719 := by
  apply lucas_primality 146803238938895719 (3 : ZMod 146803238938895719)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1439247440577409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1439247440577409, 1)] : List FactorBlock).map factorBlockValue).prod) = 146803238938895719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_17
      · exact prime_thirteenK_1439247440577409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 146803238938895719) ^ 73401619469447859 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 146803238938895719) ^ 48934412979631906 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 146803238938895719) ^ 8635484643464454 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 146803238938895719) ^ 102 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_239766403692867703 : Nat.Prime 239766403692867703 := by
  apply lucas_primality 239766403692867703 (3 : ZMod 239766403692867703)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (1753, 1), (16097, 1), (2273119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (1753, 1), (16097, 1), (2273119, 1)] : List FactorBlock).map factorBlockValue).prod) = 239766403692867703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_89
      · exact prime_thirteenK_1753
      · exact prime_thirteenK_16097
      · exact prime_thirteenK_2273119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 239766403692867703) ^ 119883201846433851 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 79922134564289234 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 34252343384695386 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 2694004535874918 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 136774902277734 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 14895098694966 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 239766403692867703) ^ 105479037258 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_377672369920211983 : Nat.Prime 377672369920211983 := by
  apply lucas_primality 377672369920211983 (3 : ZMod 377672369920211983)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 2), (5037757, 1), (14751743, 1)] : List FactorBlock).map factorBlockValue).prod) = 377672369920211983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_5037757
      · exact prime_thirteenK_14751743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 377672369920211983) ^ 188836184960105991 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 125890789973403994 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 53953195702887426 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 34333851810928362 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 74968357926 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 377672369920211983) ^ 25601881074 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_426950491054489151 : Nat.Prime 426950491054489151 := by
  apply lucas_primality 426950491054489151 (7 : ZMod 426950491054489151)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (2767, 1), (19167809209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (2767, 1), (19167809209, 1)] : List FactorBlock).map factorBlockValue).prod) = 426950491054489151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_23
      · exact prime_thirteenK_2767
      · exact prime_thirteenK_19167809209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 426950491054489151) ^ 213475245527244575 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 85390098210897830 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 60992927293498450 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 18563064828456050 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 154300864132450 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 426950491054489151) ^ 22274350 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_29
      · exact prime_thirteenK_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_61717
      · exact prime_thirteenK_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_843442522577531353 : Nat.Prime 843442522577531353 := by
  apply lucas_primality 843442522577531353 (5 : ZMod 843442522577531353)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (79, 1), (7061169065849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (79, 1), (7061169065849, 1)] : List FactorBlock).map factorBlockValue).prod) = 843442522577531353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_79
      · exact prime_thirteenK_7061169065849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 843442522577531353) ^ 421721261288765676 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 843442522577531353) ^ 281147507525843784 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 843442522577531353) ^ 120491788939647336 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 843442522577531353) ^ 10676487627563688 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 843442522577531353) ^ 119448 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1421559306659942309 : Nat.Prime 1421559306659942309 := by
  apply lucas_primality 1421559306659942309 (2 : ZMod 1421559306659942309)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (2521, 1), (548528279441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (2521, 1), (548528279441, 1)] : List FactorBlock).map factorBlockValue).prod) = 1421559306659942309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_257
      · exact prime_thirteenK_2521
      · exact prime_thirteenK_548528279441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1421559306659942309) ^ 710779653329971154 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1421559306659942309) ^ 5531359169883044 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1421559306659942309) ^ 563887071265348 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1421559306659942309) ^ 2591588 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1561827409733979467 : Nat.Prime 1561827409733979467 := by
  apply lucas_primality 1561827409733979467 (2 : ZMod 1561827409733979467)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2767, 1), (955337, 1), (22724479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2767, 1), (955337, 1), (22724479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1561827409733979467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_2767
      · exact prime_thirteenK_955337
      · exact prime_thirteenK_22724479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1561827409733979467) ^ 780913704866989733 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 120140569979536882 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 564447925454998 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 1634844468218 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1561827409733979467) ^ 68728854454 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1603952514074243401 : Nat.Prime 1603952514074243401 := by
  apply lucas_primality 1603952514074243401 (7 : ZMod 1603952514074243401)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (17, 1), (19, 1), (47, 1), (67819, 1), (2596501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (17, 1), (19, 1), (47, 1), (67819, 1), (2596501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1603952514074243401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_17
      · exact prime_thirteenK_19
      · exact prime_thirteenK_47
      · exact prime_thirteenK_67819
      · exact prime_thirteenK_2596501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1603952514074243401) ^ 801976257037121700 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 534650838024747800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 320790502814848680 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 94350147886720200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 84418553372328600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 34126649235622200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 23650489008600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603952514074243401) ^ 617736143400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1757185738698779999 : Nat.Prime 1757185738698779999 := by
  apply lucas_primality 1757185738698779999 (7 : ZMod 1757185738698779999)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (131, 1), (26387, 1), (36310173281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (131, 1), (26387, 1), (36310173281, 1)] : List FactorBlock).map factorBlockValue).prod) = 1757185738698779999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_131
      · exact prime_thirteenK_26387
      · exact prime_thirteenK_36310173281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1757185738698779999) ^ 878592869349389999 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1757185738698779999) ^ 251026534099825714 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1757185738698779999) ^ 13413631593120458 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1757185738698779999) ^ 66592857797354 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1757185738698779999) ^ 48393758 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2009831726809906421 : Nat.Prime 2009831726809906421 := by
  apply lucas_primality 2009831726809906421 (2 : ZMod 2009831726809906421)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (557, 1), (409901, 1), (440144753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (557, 1), (409901, 1), (440144753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2009831726809906421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_557
      · exact prime_thirteenK_409901
      · exact prime_thirteenK_440144753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2009831726809906421) ^ 1004915863404953210 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 401966345361981284 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 3608315487989060 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 4903212548420 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009831726809906421) ^ 4566297140 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2664323272382311283 : Nat.Prime 2664323272382311283 := by
  apply lucas_primality 2664323272382311283 (2 : ZMod 2664323272382311283)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (587, 1), (71191, 1), (1028328883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (587, 1), (71191, 1), (1028328883, 1)] : List FactorBlock).map factorBlockValue).prod) = 2664323272382311283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_31
      · exact prime_thirteenK_587
      · exact prime_thirteenK_71191
      · exact prime_thirteenK_1028328883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2664323272382311283) ^ 1332161636191155641 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2664323272382311283) ^ 85945912012332622 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2664323272382311283) ^ 4538881213598486 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2664323272382311283) ^ 37425001367902 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2664323272382311283) ^ 2590925254 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_3077167559992740997 : Nat.Prime 3077167559992740997 := by
  apply lucas_primality 3077167559992740997 (2 : ZMod 3077167559992740997)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (21569, 1), (11888851128907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (21569, 1), (11888851128907, 1)] : List FactorBlock).map factorBlockValue).prod) = 3077167559992740997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_21569
      · exact prime_thirteenK_11888851128907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3077167559992740997) ^ 1538583779996370498 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 1025722519997580332 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 142666213546884 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3077167559992740997) ^ 258828 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_3889302824472379117 : Nat.Prime 3889302824472379117 := by
  apply lucas_primality 3889302824472379117 (2 : ZMod 3889302824472379117)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (29464415336911963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (29464415336911963, 1)] : List FactorBlock).map factorBlockValue).prod) = 3889302824472379117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_29464415336911963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3889302824472379117) ^ 1944651412236189558 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3889302824472379117) ^ 1296434274824126372 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3889302824472379117) ^ 353572984042943556 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3889302824472379117) ^ 132 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_4018378747686678983 : Nat.Prime 4018378747686678983 := by
  apply lucas_primality 4018378747686678983 (5 : ZMod 4018378747686678983)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (193, 1), (14419, 1), (4598633189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (193, 1), (14419, 1), (4598633189, 1)] : List FactorBlock).map factorBlockValue).prod) = 4018378747686678983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_157
      · exact prime_thirteenK_193
      · exact prime_thirteenK_14419
      · exact prime_thirteenK_4598633189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4018378747686678983) ^ 2009189373843339491 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 25594769093545726 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 20820615272987974 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 278686368519778 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4018378747686678983) ^ 873820238 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_6026129309866944227 : Nat.Prime 6026129309866944227 := by
  apply lucas_primality 6026129309866944227 (2 : ZMod 6026129309866944227)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (10861, 1), (1123160144339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (10861, 1), (1123160144339, 1)] : List FactorBlock).map factorBlockValue).prod) = 6026129309866944227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_19
      · exact prime_thirteenK_10861
      · exact prime_thirteenK_1123160144339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6026129309866944227) ^ 3013064654933472113 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6026129309866944227) ^ 463548408451303402 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6026129309866944227) ^ 317164700519312854 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6026129309866944227) ^ 554841111303466 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6026129309866944227) ^ 5365334 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_6276586759550679409 : Nat.Prime 6276586759550679409 := by
  apply lucas_primality 6276586759550679409 (7 : ZMod 6276586759550679409)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (254927, 1), (11928834361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (254927, 1), (11928834361, 1)] : List FactorBlock).map factorBlockValue).prod) = 6276586759550679409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_43
      · exact prime_thirteenK_254927
      · exact prime_thirteenK_11928834361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6276586759550679409) ^ 3138293379775339704 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 2092195586516893136 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 145967133943039056 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 24621114121104 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 6276586759550679409) ^ 526169328 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_7777367187437459221 : Nat.Prime 7777367187437459221 := by
  apply lucas_primality 7777367187437459221 (6 : ZMod 7777367187437459221)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (50456514775123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (50456514775123, 1)] : List FactorBlock).map factorBlockValue).prod) = 7777367187437459221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_367
      · exact prime_thirteenK_50456514775123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7777367187437459221) ^ 3888683593718729610 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 2592455729145819740 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 1555473437487491844 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 1111052455348208460 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 21191736205551660 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7777367187437459221) ^ 154140 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_10675900157669865007 : Nat.Prime 10675900157669865007 := by
  apply lucas_primality 10675900157669865007 (10 : ZMod 10675900157669865007)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 2), (1823, 1), (3271, 1), (118081211, 1)] : List FactorBlock).map factorBlockValue).prod) = 10675900157669865007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_7
      · exact prime_thirteenK_19
      · exact prime_thirteenK_1823
      · exact prime_thirteenK_3271
      · exact prime_thirteenK_118081211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10675900157669865007) ^ 5337950078834932503 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3558633385889955002 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 1525128593952837858 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 561889481982624474 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 5856226087586322 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 3263803166514786 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 10675900157669865007) ^ 90411506346 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_13145780685211854149 : Nat.Prime 13145780685211854149 := by
  apply lucas_primality 13145780685211854149 (2 : ZMod 13145780685211854149)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (67, 1), (226043412291283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (67, 1), (226043412291283, 1)] : List FactorBlock).map factorBlockValue).prod) = 13145780685211854149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_31
      · exact prime_thirteenK_67
      · exact prime_thirteenK_226043412291283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13145780685211854149) ^ 6572890342605927074 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 1877968669315979164 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 424057441458446908 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 196205681868833644 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13145780685211854149) ^ 58156 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_14121180779525611873 : Nat.Prime 14121180779525611873 := by
  apply lucas_primality 14121180779525611873 (5 : ZMod 14121180779525611873)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (6395462309567759, 1)] : List FactorBlock).map factorBlockValue).prod) = 14121180779525611873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_23
      · exact prime_thirteenK_6395462309567759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14121180779525611873) ^ 7060590389762805936 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 4707060259841870624 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 613964381718504864 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 14121180779525611873) ^ 2208 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_17389510759726903703 : Nat.Prime 17389510759726903703 := by
  apply lucas_primality 17389510759726903703 (5 : ZMod 17389510759726903703)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (256889, 1), (1091817788989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (256889, 1), (1091817788989, 1)] : List FactorBlock).map factorBlockValue).prod) = 17389510759726903703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_31
      · exact prime_thirteenK_256889
      · exact prime_thirteenK_1091817788989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17389510759726903703) ^ 8694755379863451851 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17389510759726903703) ^ 560951959991190442 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17389510759726903703) ^ 67692702917318 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 17389510759726903703) ^ 15927118 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_22091144538306559019 : Nat.Prime 22091144538306559019 := by
  apply lucas_primality 22091144538306559019 (2 : ZMod 22091144538306559019)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (190277159, 1), (384436501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (190277159, 1), (384436501, 1)] : List FactorBlock).map factorBlockValue).prod) = 22091144538306559019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_151
      · exact prime_thirteenK_190277159
      · exact prime_thirteenK_384436501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22091144538306559019) ^ 11045572269153279509 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22091144538306559019) ^ 146298970452361318 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22091144538306559019) ^ 116099823302 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22091144538306559019) ^ 57463702018 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_46854822292019384011 : Nat.Prime 46854822292019384011 := by
  apply lucas_primality 46854822292019384011 (2 : ZMod 46854822292019384011)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1561827409733979467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1561827409733979467, 1)] : List FactorBlock).map factorBlockValue).prod) = 46854822292019384011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_1561827409733979467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46854822292019384011) ^ 23427411146009692005 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 15618274097339794670 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 9370964458403876802 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46854822292019384011) ^ 30 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_53586317083186147097 : Nat.Prime 53586317083186147097 := by
  apply lucas_primality 53586317083186147097 (3 : ZMod 53586317083186147097)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19001, 1), (488321, 1), (721908347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19001, 1), (488321, 1), (721908347, 1)] : List FactorBlock).map factorBlockValue).prod) = 53586317083186147097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_19001
      · exact prime_thirteenK_488321
      · exact prime_thirteenK_721908347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53586317083186147097) ^ 26793158541593073548 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 53586317083186147097) ^ 2820184047323096 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 53586317083186147097) ^ 109735844010776 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 53586317083186147097) ^ 74228698568 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_67337590816601618489 : Nat.Prime 67337590816601618489 := by
  apply lucas_primality 67337590816601618489 (6 : ZMod 67337590816601618489)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (71, 1), (9269333, 1), (752335981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (71, 1), (9269333, 1), (752335981, 1)] : List FactorBlock).map factorBlockValue).prod) = 67337590816601618489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_17
      · exact prime_thirteenK_71
      · exact prime_thirteenK_9269333
      · exact prime_thirteenK_752335981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 67337590816601618489) ^ 33668795408300809244 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 3961034753917742264 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 948416772064811528 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 7264556232536 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 67337590816601618489) ^ 89504679448 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_130004395631094960253 : Nat.Prime 130004395631094960253 := by
  apply lucas_primality 130004395631094960253 (2 : ZMod 130004395631094960253)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (146173, 1), (24705200084659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (146173, 1), (24705200084659, 1)] : List FactorBlock).map factorBlockValue).prod) = 130004395631094960253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_146173
      · exact prime_thirteenK_24705200084659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 130004395631094960253) ^ 65002197815547480126 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 43334798543698320084 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 889387203047724 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130004395631094960253) ^ 5262228 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_202083720657442576003 : Nat.Prime 202083720657442576003 := by
  apply lucas_primality 202083720657442576003 (3 : ZMod 202083720657442576003)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (103, 1), (881, 1), (4266263672987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (103, 1), (881, 1), (4266263672987, 1)] : List FactorBlock).map factorBlockValue).prod) = 202083720657442576003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_29
      · exact prime_thirteenK_103
      · exact prime_thirteenK_881
      · exact prime_thirteenK_4266263672987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 202083720657442576003) ^ 101041860328721288001 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 202083720657442576003) ^ 67361240219147525334 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 202083720657442576003) ^ 6968404160601468138 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 202083720657442576003) ^ 1961977870460607534 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 202083720657442576003) ^ 229379932641819042 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 202083720657442576003) ^ 47367846 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_293940157940180816303 : Nat.Prime 293940157940180816303 := by
  apply lucas_primality 293940157940180816303 (5 : ZMod 293940157940180816303)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (71, 1), (821, 1), (18043, 1), (688371109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (71, 1), (821, 1), (18043, 1), (688371109, 1)] : List FactorBlock).map factorBlockValue).prod) = 293940157940180816303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_29
      · exact prime_thirteenK_71
      · exact prime_thirteenK_821
      · exact prime_thirteenK_18043
      · exact prime_thirteenK_688371109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 293940157940180816303) ^ 146970078970090408151 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 293940157940180816303) ^ 41991451134311545186 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 293940157940180816303) ^ 10135867515178648838 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 293940157940180816303) ^ 4140002224509588962 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 293940157940180816303) ^ 358026988964897462 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 293940157940180816303) ^ 16291091167775914 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 293940157940180816303) ^ 427008272278 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_321517902499116882583 : Nat.Prime 321517902499116882583 := by
  apply lucas_primality 321517902499116882583 (3 : ZMod 321517902499116882583)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53586317083186147097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53586317083186147097, 1)] : List FactorBlock).map factorBlockValue).prod) = 321517902499116882583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_53586317083186147097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 321517902499116882583) ^ 160758951249558441291 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 321517902499116882583) ^ 107172634166372294194 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 321517902499116882583) ^ 6 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_330894500568270950627 : Nat.Prime 330894500568270950627 := by
  apply lucas_primality 330894500568270950627 (2 : ZMod 330894500568270950627)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (146803238938895719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (146803238938895719, 1)] : List FactorBlock).map factorBlockValue).prod) = 330894500568270950627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_23
      · exact prime_thirteenK_146803238938895719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 330894500568270950627) ^ 165447250284135475313 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 330894500568270950627) ^ 47270642938324421518 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 330894500568270950627) ^ 14386717416011780462 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 330894500568270950627) ^ 2254 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_458277287644781321513 : Nat.Prime 458277287644781321513 := by
  apply lucas_primality 458277287644781321513 (3 : ZMod 458277287644781321513)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (8297, 1), (6904261896540637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (8297, 1), (6904261896540637, 1)] : List FactorBlock).map factorBlockValue).prod) = 458277287644781321513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_8297
      · exact prime_thirteenK_6904261896540637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 458277287644781321513) ^ 229138643822390660756 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 458277287644781321513) ^ 55234095172325096 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 458277287644781321513) ^ 66376 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_749677156672310144177 : Nat.Prime 749677156672310144177 := by
  apply lucas_primality 749677156672310144177 (3 : ZMod 749677156672310144177)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (46854822292019384011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (46854822292019384011, 1)] : List FactorBlock).map factorBlockValue).prod) = 749677156672310144177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_46854822292019384011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 749677156672310144177) ^ 374838578336155072088 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 749677156672310144177) ^ 16 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_924096500249201382167 : Nat.Prime 924096500249201382167 := by
  apply lucas_primality 924096500249201382167 (5 : ZMod 924096500249201382167)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1223, 1), (168197789, 1), (320879927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1223, 1), (168197789, 1), (320879927, 1)] : List FactorBlock).map factorBlockValue).prod) = 924096500249201382167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_1223
      · exact prime_thirteenK_168197789
      · exact prime_thirteenK_320879927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 924096500249201382167) ^ 462048250124600691083 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 132013785749885911738 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 755598119582339642 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 5494106110094 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 924096500249201382167) ^ 2879882543258 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2124561888099414885917 : Nat.Prime 2124561888099414885917 := by
  apply lucas_primality 2124561888099414885917 (2 : ZMod 2124561888099414885917)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (10801067, 1), (375380267527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (10801067, 1), (375380267527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2124561888099414885917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_131
      · exact prime_thirteenK_10801067
      · exact prime_thirteenK_375380267527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2124561888099414885917) ^ 1062280944049707442958 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 16218029680148205236 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 196699260184148 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2124561888099414885917) ^ 5659759108 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_19
      · exact prime_thirteenK_107
      · exact prime_thirteenK_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_3720151109024930829341 : Nat.Prime 3720151109024930829341 := by
  apply lucas_primality 3720151109024930829341 (10 : ZMod 3720151109024930829341)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (1873, 1), (1091318243936369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (1873, 1), (1091318243936369, 1)] : List FactorBlock).map factorBlockValue).prod) = 3720151109024930829341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_13
      · exact prime_thirteenK_1873
      · exact prime_thirteenK_1091318243936369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3720151109024930829341) ^ 1860075554512465414670 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 744030221804986165868 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 531450158432132975620 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 286165469924994679180 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 1986199203964191580 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3720151109024930829341) ^ 3408860 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_9621288441620920343779 : Nat.Prime 9621288441620920343779 := by
  apply lucas_primality 9621288441620920343779 (3 : ZMod 9621288441620920343779)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (2689, 1), (19236651994427557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (2689, 1), (19236651994427557, 1)] : List FactorBlock).map factorBlockValue).prod) = 9621288441620920343779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_31
      · exact prime_thirteenK_2689
      · exact prime_thirteenK_19236651994427557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9621288441620920343779) ^ 4810644220810460171889 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9621288441620920343779) ^ 3207096147206973447926 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9621288441620920343779) ^ 310364143278094204638 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9621288441620920343779) ^ 3578017270963525602 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9621288441620920343779) ^ 500154 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_14715695298318302263009 : Nat.Prime 14715695298318302263009 := by
  apply lucas_primality 14715695298318302263009 (7 : ZMod 14715695298318302263009)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (23, 1), (181, 1), (1153, 1), (2903228044637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (23, 1), (181, 1), (1153, 1), (2903228044637, 1)] : List FactorBlock).map factorBlockValue).prod) = 14715695298318302263009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_23
      · exact prime_thirteenK_181
      · exact prime_thirteenK_1153
      · exact prime_thirteenK_2903228044637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14715695298318302263009) ^ 7357847649159151131504 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 4905231766106100754336 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 1337790481665300205728 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 639812839057317489696 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 81302183968609404768 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 12762962097413965536 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 14715695298318302263009) ^ 5068735584 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_16764676135348824717077 : Nat.Prime 16764676135348824717077 := by
  apply lucas_primality 16764676135348824717077 (2 : ZMod 16764676135348824717077)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (149, 1), (4018378747686678983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (149, 1), (4018378747686678983, 1)] : List FactorBlock).map factorBlockValue).prod) = 16764676135348824717077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_7
      · exact prime_thirteenK_149
      · exact prime_thirteenK_4018378747686678983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16764676135348824717077) ^ 8382338067674412358538 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 2394953733621260673868 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 112514604935227011524 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16764676135348824717077) ^ 4172 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_24026509006479235936343 : Nat.Prime 24026509006479235936343 := by
  apply lucas_primality 24026509006479235936343 (5 : ZMod 24026509006479235936343)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (924096500249201382167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (924096500249201382167, 1)] : List FactorBlock).map factorBlockValue).prod) = 24026509006479235936343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_13
      · exact prime_thirteenK_924096500249201382167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 24026509006479235936343) ^ 12013254503239617968171 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24026509006479235936343) ^ 1848193000498402764334 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 24026509006479235936343) ^ 26 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_29981896109898443262907 : Nat.Prime 29981896109898443262907 := by
  apply lucas_primality 29981896109898443262907 (2 : ZMod 29981896109898443262907)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (293940157940180816303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (293940157940180816303, 1)] : List FactorBlock).map factorBlockValue).prod) = 29981896109898443262907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_17
      · exact prime_thirteenK_293940157940180816303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29981896109898443262907) ^ 14990948054949221631453 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29981896109898443262907) ^ 9993965369966147754302 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29981896109898443262907) ^ 1763640947641084897818 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29981896109898443262907) ^ 102 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_48053018012958471872687 : Nat.Prime 48053018012958471872687 := by
  apply lucas_primality 48053018012958471872687 (5 : ZMod 48053018012958471872687)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24026509006479235936343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24026509006479235936343, 1)] : List FactorBlock).map factorBlockValue).prod) = 48053018012958471872687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_24026509006479235936343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 48053018012958471872687) ^ 24026509006479235936343 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 48053018012958471872687) ^ 2 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_57390524797284178703339 : Nat.Prime 57390524797284178703339 := by
  apply lucas_primality 57390524797284178703339 (2 : ZMod 57390524797284178703339)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3259, 1), (1602863, 1), (5493250906657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3259, 1), (1602863, 1), (5493250906657, 1)] : List FactorBlock).map factorBlockValue).prod) = 57390524797284178703339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3259
      · exact prime_thirteenK_1602863
      · exact prime_thirteenK_5493250906657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57390524797284178703339) ^ 28695262398642089351669 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 57390524797284178703339) ^ 17609857255993917982 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 57390524797284178703339) ^ 35805009409590326 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 57390524797284178703339) ^ 10447461034 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_90753507406596180058621 : Nat.Prime 90753507406596180058621 := by
  apply lucas_primality 90753507406596180058621 (10 : ZMod 90753507406596180058621)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (251, 1), (6026129309866944227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (251, 1), (6026129309866944227, 1)] : List FactorBlock).map factorBlockValue).prod) = 90753507406596180058621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_251
      · exact prime_thirteenK_6026129309866944227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 90753507406596180058621) ^ 45376753703298090029310 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 90753507406596180058621) ^ 30251169135532060019540 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 90753507406596180058621) ^ 18150701481319236011724 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 90753507406596180058621) ^ 361567758592016653620 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (10 : ZMod 90753507406596180058621) ^ 15060 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_109858826130696412328971 : Nat.Prime 109858826130696412328971 := by
  apply lucas_primality 109858826130696412328971 (2 : ZMod 109858826130696412328971)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (1187, 1), (27793292736046007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (1187, 1), (27793292736046007, 1)] : List FactorBlock).map factorBlockValue).prod) = 109858826130696412328971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_37
      · exact prime_thirteenK_1187
      · exact prime_thirteenK_27793292736046007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 109858826130696412328971) ^ 54929413065348206164485 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 36619608710232137442990 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 21971765226139282465794 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 2969157462991794927810 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 92551664811033203310 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 109858826130696412328971) ^ 3952710 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_139027313372561641588853 : Nat.Prime 139027313372561641588853 := by
  apply lucas_primality 139027313372561641588853 (2 : ZMod 139027313372561641588853)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (107, 1), (6203, 1), (3080389673224709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (107, 1), (6203, 1), (3080389673224709, 1)] : List FactorBlock).map factorBlockValue).prod) = 139027313372561641588853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_17
      · exact prime_thirteenK_107
      · exact prime_thirteenK_6203
      · exact prime_thirteenK_3080389673224709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139027313372561641588853) ^ 69513656686280820794426 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 8178077257209508328756 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 1299320685724875155036 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 22412915262382982684 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 139027313372561641588853) ^ 45133028 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_615862698082092061133503 : Nat.Prime 615862698082092061133503 := by
  apply lucas_primality 615862698082092061133503 (6 : ZMod 615862698082092061133503)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (107, 1), (2410589, 1), (6523728322439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (107, 1), (2410589, 1), (6523728322439, 1)] : List FactorBlock).map factorBlockValue).prod) = 615862698082092061133503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_61
      · exact prime_thirteenK_107
      · exact prime_thirteenK_2410589
      · exact prime_thirteenK_6523728322439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 615862698082092061133503) ^ 307931349041046030566751 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 615862698082092061133503) ^ 205287566027364020377834 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 615862698082092061133503) ^ 10096109804624460018582 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 615862698082092061133503) ^ 5755726150299925804986 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 615862698082092061133503) ^ 255482248563356118 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (6 : ZMod 615862698082092061133503) ^ 94403486418 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_720252565412469632018731 : Nat.Prime 720252565412469632018731 := by
  apply lucas_primality 720252565412469632018731 (2 : ZMod 720252565412469632018731)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (661, 1), (2220277, 1), (5452977238001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (661, 1), (2220277, 1), (5452977238001, 1)] : List FactorBlock).map factorBlockValue).prod) = 720252565412469632018731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_661
      · exact prime_thirteenK_2220277
      · exact prime_thirteenK_5452977238001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 720252565412469632018731) ^ 360126282706234816009365 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 240084188470823210672910 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 144050513082493926403746 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 1089640794875143164930 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 324397615888679490 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (2 : ZMod 720252565412469632018731) ^ 132084278730 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1121040809141990479770073 : Nat.Prime 1121040809141990479770073 := by
  apply lucas_primality 1121040809141990479770073 (5 : ZMod 1121040809141990479770073)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (1733, 1), (1801, 1), (39581, 1), (19900204619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (1733, 1), (1801, 1), (39581, 1), (19900204619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121040809141990479770073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_19
      · exact prime_thirteenK_1733
      · exact prime_thirteenK_1801
      · exact prime_thirteenK_39581
      · exact prime_thirteenK_19900204619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1121040809141990479770073) ^ 560520404570995239885036 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 373680269713996826590024 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 59002147849578446303688 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 646878712718978926584 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 622454641389222920472 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 28322700516459677112 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121040809141990479770073) ^ 56333129764488 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_9175802682589068344864299 : Nat.Prime 9175802682589068344864299 := by
  apply lucas_primality 9175802682589068344864299 (3 : ZMod 9175802682589068344864299)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (139027313372561641588853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (139027313372561641588853, 1)] : List FactorBlock).map factorBlockValue).prod) = 9175802682589068344864299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_11
      · exact prime_thirteenK_139027313372561641588853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9175802682589068344864299) ^ 4587901341294534172432149 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 3058600894196356114954766 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 834163880235369849533118 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9175802682589068344864299) ^ 66 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_165263112831577306211265601 : Nat.Prime 165263112831577306211265601 := by
  apply lucas_primality 165263112831577306211265601 (71 : ZMod 165263112831577306211265601)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 165263112831577306211265601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_19
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_37
      · exact prime_thirteenK_41
      · exact prime_thirteenK_43
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53
      · exact prime_thirteenK_59
      · exact prime_thirteenK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 165263112831577306211265601) ^ 82631556415788653105632800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 55087704277192435403755200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 33052622566315461242253120 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 23609016118796758030180800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 15023919348325209655569600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 12712547140890562016251200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 9721359578328076835956800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 8698058570083016116382400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 7185352731807708965707200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 5698728028675079524526400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 4466570617069656924628800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 4030807630038470883201600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 3843328205385518749099200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 3516236443225049068324800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 3118171940218439739835200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 2801069709009784851038400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (71 : ZMod 165263112831577306211265601) ^ 2709231357894709937889600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_180817288156902229148796481 : Nat.Prime 180817288156902229148796481 := by
  apply lucas_primality 180817288156902229148796481 (79 : ZMod 180817288156902229148796481)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 180817288156902229148796481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_19
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_31
      · exact prime_thirteenK_37
      · exact prime_thirteenK_41
      · exact prime_thirteenK_43
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53
      · exact prime_thirteenK_59
      · exact prime_thirteenK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 180817288156902229148796481) ^ 90408644078451114574398240 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 60272429385634076382932160 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 36163457631380445829759296 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 25831041165271747021256640 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 16437935286991111740799680 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 13909022165915556088368960 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 9516699376679064692041920 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 7861621224213140397773760 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 6235078901962145832717120 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 5832815746996846101574080 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 4886953733970330517535040 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 4410177759924444613385280 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 4205053212951214631367360 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 3847176343763877215931840 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 3411646946356645832996160 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 3064699799269529307606720 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (79 : ZMod 180817288156902229148796481) ^ 2964217838637741461455680 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_192118368666708618470596261 : Nat.Prime 192118368666708618470596261 := by
  apply lucas_primality 192118368666708618470596261 (14 : ZMod 192118368666708618470596261)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 192118368666708618470596261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_19
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_31
      · exact prime_thirteenK_37
      · exact prime_thirteenK_41
      · exact prime_thirteenK_43
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53
      · exact prime_thirteenK_59
      · exact prime_thirteenK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 192118368666708618470596261) ^ 96059184333354309235298130 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 64039456222236206156865420 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 38423673733341723694119252 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 27445481238101231210085180 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 17465306242428056224599660 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 14778336051285278343892020 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 11301080509806389321799780 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 10111493087721506235294540 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 8352972550726461672634620 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 6624771333334779947261940 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 6197366731184148982922460 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 5192388342343476174880980 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 4685813869919722401721860 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 4467869038760665545827820 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 4087624865249119541927580 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 3624874880503936197558420 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 3256243536723874889332140 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (14 : ZMod 192118368666708618470596261) ^ 3149481453552600302796660 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_274454812381012312100851801 : Nat.Prime 274454812381012312100851801 := by
  apply lucas_primality 274454812381012312100851801 (73 : ZMod 274454812381012312100851801)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 2), (7, 1), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 274454812381012312100851801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_19
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_31
      · exact prime_thirteenK_37
      · exact prime_thirteenK_41
      · exact prime_thirteenK_43
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53
      · exact prime_thirteenK_59
      · exact prime_thirteenK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 274454812381012312100851801) ^ 137227406190506156050425900 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 91484937460337437366950600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 54890962476202462420170360 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 39207830340144616014407400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 24950437489182937463713800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 21111908644693254776988600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 16144400728294841888285400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 14444990125316437478992200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 11932817929609230960906600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 9463959047621114210374200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 8853381044548784261317800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 7417697631919251678401400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 6694019814171032002459800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 6382670055372379351182600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 5839464093213027917039400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 5178392686434194567940600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 4651776481034106984760200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (73 : ZMod 274454812381012312100851801) ^ 4499259219360857575423800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_384236737333417236941192521 : Nat.Prime 384236737333417236941192521 := by
  apply lucas_primality 384236737333417236941192521 (107 : ZMod 384236737333417236941192521)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 384236737333417236941192521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_19
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_31
      · exact prime_thirteenK_37
      · exact prime_thirteenK_41
      · exact prime_thirteenK_43
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53
      · exact prime_thirteenK_59
      · exact prime_thirteenK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 384236737333417236941192521) ^ 192118368666708618470596260 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 128078912444472412313730840 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 76847347466683447388238504 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 54890962476202462420170360 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 34930612484856112449199320 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 29556672102570556687784040 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 22602161019612778643599560 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 20222986175443012470589080 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 16705945101452923345269240 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 13249542666669559894523880 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 12394733462368297965844920 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 10384776684686952349761960 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 9371627739839444803443720 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 8935738077521331091655640 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 8175249730498239083855160 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 7249749761007872395116840 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 6512487073447749778664280 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (107 : ZMod 384236737333417236941192521) ^ 6298962907105200605593320 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_394088961367607422503787201 : Nat.Prime 394088961367607422503787201 := by
  apply lucas_primality 394088961367607422503787201 (103 : ZMod 394088961367607422503787201)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 394088961367607422503787201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_19
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_31
      · exact prime_thirteenK_37
      · exact prime_thirteenK_41
      · exact prime_thirteenK_43
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53
      · exact prime_thirteenK_59
      · exact prime_thirteenK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 394088961367607422503787201) ^ 197044480683803711251893600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 131362987122535807501262400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 78817792273521484500757440 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 56298423052515346071969600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 35826269215237038409435200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 30314535489815955577214400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 23181703609859260147281600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 20741524282505653815988800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 17134302668156844456686400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 13589274529917497327716800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 12712547140890562016251200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 10651053009935335743345600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9611925887014815183019200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 9164859566688544709390400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 8384871518459732393697600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 7435640780520894764222400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6679473921484871567860800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (103 : ZMod 394088961367607422503787201) ^ 6460474776518154467275200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_404459723508860249411781601 : Nat.Prime 404459723508860249411781601 := by
  apply lucas_primality 404459723508860249411781601 (89 : ZMod 404459723508860249411781601)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 404459723508860249411781601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_31
      · exact prime_thirteenK_37
      · exact prime_thirteenK_41
      · exact prime_thirteenK_43
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53
      · exact prime_thirteenK_59
      · exact prime_thirteenK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 404459723508860249411781601) ^ 202229861754430124705890800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 134819907836286749803927200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 80891944701772049882356320 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 57779960501265749915968800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 36769065773532749946525600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 31112286423758480723983200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 23791748441697661730104800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 17585205369950445626599200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 13946887017546905152130400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 13047087855124524174573600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 10931343878617844578696800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 9864871305094152424677600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 9406040081601401149111200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 8605526032103409561952800 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 7631315537903023573807200 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 6855249550997631345962400 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (89 : ZMod 404459723508860249411781601) ^ 6630487270637053269045600 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_1024631299555779298509846721 : Nat.Prime 1024631299555779298509846721 := by
  apply lucas_primality 1024631299555779298509846721 (67 : ZMod 1024631299555779298509846721)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024631299555779298509846721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_11
      · exact prime_thirteenK_13
      · exact prime_thirteenK_17
      · exact prime_thirteenK_19
      · exact prime_thirteenK_23
      · exact prime_thirteenK_29
      · exact prime_thirteenK_31
      · exact prime_thirteenK_37
      · exact prime_thirteenK_41
      · exact prime_thirteenK_43
      · exact prime_thirteenK_47
      · exact prime_thirteenK_53
      · exact prime_thirteenK_59
      · exact prime_thirteenK_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 1024631299555779298509846721) ^ 512315649777889649254923360 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 341543766518593099503282240 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 204926259911155859701969344 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 146375899936539899787120960 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 93148299959616299864531520 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 78817792273521484500757440 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 60272429385634076382932160 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 53927963134514699921570880 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 44549186937207795587384640 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 35332113777785493052063680 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 33052622566315461242253120 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 27692737825831872932698560 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 24991007306238519475849920 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 23828634873390216244415040 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 21800665947995304223613760 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 19332666029354326386978240 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 17366632195860666076438080 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (67 : ZMod 1024631299555779298509846721) ^ 16797234418947201614915520 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_15369469493336689477647700871 : Nat.Prime 15369469493336689477647700871 := by
  apply lucas_primality 15369469493336689477647700871 (7 : ZMod 15369469493336689477647700871)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (193, 2), (785903, 1), (7500276474838703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (193, 2), (785903, 1), (7500276474838703, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_5
      · exact prime_thirteenK_7
      · exact prime_thirteenK_193
      · exact prime_thirteenK_785903
      · exact prime_thirteenK_7500276474838703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15369469493336689477647700871) ^ 7684734746668344738823850435 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700871) ^ 3073893898667337895529540174 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700871) ^ 2195638499048098496806814410 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700871) ^ 79634556960293727863459590 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700871) ^ 19556445888788679363290 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700871) ^ 2049187059290 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_15369469493336689477647700873 : Nat.Prime 15369469493336689477647700873 := by
  apply lucas_primality 15369469493336689477647700873 (7 : ZMod 15369469493336689477647700873)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4889, 1), (5119, 1), (562403069, 1), (15166086619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4889, 1), (5119, 1), (562403069, 1), (15166086619, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_3
      · exact prime_thirteenK_4889
      · exact prime_thirteenK_5119
      · exact prime_thirteenK_562403069
      · exact prime_thirteenK_15166086619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15369469493336689477647700873) ^ 7684734746668344738823850436 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700873) ^ 5123156497778896492549233624 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700873) ^ 3143683676280771011995848 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700873) ^ 3002435923683666629741688 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700873) ^ 27328210567315893288 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (7 : ZMod 15369469493336689477647700873) ^ 1013410372724753688 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem prime_thirteenK_15369469493336689477647700889 : Nat.Prime 15369469493336689477647700889 := by
  apply lucas_primality 15369469493336689477647700889 (3 : ZMod 15369469493336689477647700889)
  · rw [← thirteenKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (372023, 1), (292379671, 1), (1605680900297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (372023, 1), (292379671, 1), (1605680900297, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirteenK_2
      · exact prime_thirteenK_11
      · exact prime_thirteenK_372023
      · exact prime_thirteenK_292379671
      · exact prime_thirteenK_1605680900297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15369469493336689477647700889) ^ 7684734746668344738823850444 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 15369469493336689477647700889) ^ 1397224499394244497967972808 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 15369469493336689477647700889) ^ 41313223895664218281256 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 15369469493336689477647700889) ^ 52566819850264793128 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide
    · change (3 : ZMod 15369469493336689477647700889) ^ 9571932686310104 ≠ 1
      rw [← thirteenKFastPow_eq_pow]
      decide

private theorem phi_thirteenK_15369469493336689477647700800 : Nat.totient 15369469493336689477647700800 = 2022427789971688312012800000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_5, prime_thirteenK_7, prime_thirteenK_11, prime_thirteenK_13, prime_thirteenK_17, prime_thirteenK_19, prime_thirteenK_23, prime_thirteenK_29, prime_thirteenK_31, prime_thirteenK_37, prime_thirteenK_41, prime_thirteenK_43, prime_thirteenK_47, prime_thirteenK_53, prime_thirteenK_59, prime_thirteenK_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700801 : Nat.totient 15369469493336689477647700801 = 15353814775218152739085008000 := by
  rw [← show ((([(1021, 1), (25951, 1), (1582963, 1), (366444555641737, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_1021, prime_thirteenK_25951, prime_thirteenK_1582963, prime_thirteenK_366444555641737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700802 : Nat.totient 15369469493336689477647700802 = 7682970927409204093673086080 := by
  rw [← show ((([(2, 1), (4357, 1), (148272073, 1), (11895479753831941, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_4357, prime_thirteenK_148272073, prime_thirteenK_11895479753831941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700803 : Nat.totient 15369469493336689477647700803 = 10245977729715976398070460064 := by
  rw [← show ((([(3, 1), (32029, 1), (667123, 1), (239766403692867703, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_32029, prime_thirteenK_667123, prime_thirteenK_239766403692867703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700804 : Nat.totient 15369469493336689477647700804 = 7641342182041881880577472000 := by
  rw [← show ((([(2, 2), (199, 1), (2311, 1), (5209, 1), (1603952514074243401, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_199, prime_thirteenK_2311, prime_thirteenK_5209, prime_thirteenK_1603952514074243401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700805 : Nat.totient 15369469493336689477647700805 = 12292468809755109184865829888 := by
  rw [← show ((([(5, 1), (4093, 1), (119653, 1), (6276586759550679409, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_5, prime_thirteenK_4093, prime_thirteenK_119653, prime_thirteenK_6276586759550679409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700806 : Nat.totient 15369469493336689477647700806 = 5118079365278606692764489600 := by
  rw [← show ((([(2, 1), (3, 1), (1093, 1), (21611, 1), (39791, 1), (209623, 1), (13001360959, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_1093, prime_thirteenK_21611, prime_thirteenK_39791, prime_thirteenK_209623, prime_thirteenK_13001360959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700807 : Nat.totient 15369469493336689477647700807 = 13173830994107789172433960224 := by
  rw [← show ((([(7, 1), (72863556869, 1), (30133561870930829, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_7, prime_thirteenK_72863556869, prime_thirteenK_30133561870930829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700808 : Nat.totient 15369469493336689477647700808 = 7684734744960542756606770000 := by
  rw [← show ((([(2, 3), (4499780951, 1), (426950491054489151, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_4499780951, prime_thirteenK_426950491054489151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700809 : Nat.totient 15369469493336689477647700809 = 10241991480165318167306340600 := by
  rw [← show ((([(3, 2), (2371, 1), (720252565412469632018731, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_2371, prime_thirteenK_720252565412469632018731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700810 : Nat.totient 15369469493336689477647700810 = 6147772916730239691334110400 := by
  rw [← show ((([(2, 1), (5, 1), (413141, 1), (3720151109024930829341, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_5, prime_thirteenK_413141, prime_thirteenK_3720151109024930829341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700811 : Nat.totient 15369469493336689477647700811 = 13972223748323563985524292320 := by
  rw [← show ((([(11, 1), (657653, 1), (2124561888099414885917, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_11, prime_thirteenK_657653, prime_thirteenK_2124561888099414885917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700812 : Nat.totient 15369469493336689477647700812 = 5123156466669427742140670400 := by
  rw [← show ((([(2, 2), (3, 1), (164681581, 1), (7777367187437459221, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_164681581, prime_thirteenK_7777367187437459221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700813 : Nat.totient 15369469493336689477647700813 = 14046657934239547674011714304 := by
  rw [← show ((([(13, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_13, prime_thirteenK_103, prime_thirteenK_5009, prime_thirteenK_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700814 : Nat.totient 15369469493336689477647700814 = 6586915418269611378648251424 := by
  rw [← show ((([(2, 1), (7, 1), (83511149, 1), (13145780685211854149, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_7, prime_thirteenK_83511149, prime_thirteenK_13145780685211854149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700815 : Nat.totient 15369469493336689477647700815 = 8197050396446234388078773760 := by
  rw [← show ((([(3, 1), (5, 1), (1024631299555779298509846721, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_5, prime_thirteenK_1024631299555779298509846721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700816 : Nat.totient 15369469493336689477647700816 = 7683042605184630217692813312 := by
  rw [← show ((([(2, 4), (7057, 1), (15373, 1), (74323, 1), (119134327776067, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_7057, prime_thirteenK_15373, prime_thirteenK_74323, prime_thirteenK_119134327776067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700817 : Nat.totient 15369469493336689477647700817 = 14462819214819577686848332800 := by
  rw [← show ((([(17, 1), (9437, 1), (20023, 1), (46861, 1), (102102247358591, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_17, prime_thirteenK_9437, prime_thirteenK_20023, prime_thirteenK_46861, prime_thirteenK_102102247358591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700818 : Nat.totient 15369469493336689477647700818 = 5122750510220043038495747040 := by
  rw [← show ((([(2, 1), (3, 2), (12619, 1), (212140652989, 1), (318960960511, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_12619, prime_thirteenK_212140652989, prime_thirteenK_318960960511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700819 : Nat.totient 15369469493336689477647700819 = 14556133525512236728237596000 := by
  rw [← show ((([(19, 1), (3391, 1), (118691, 1), (2009831726809906421, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_19, prime_thirteenK_3391, prime_thirteenK_118691, prime_thirteenK_2009831726809906421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700820 : Nat.totient 15369469493336689477647700820 = 6147466807584372417252864000 := by
  rw [← show ((([(2, 2), (5, 1), (19387, 1), (1584001, 1), (25024350819790243, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_5, prime_thirteenK_19387, prime_thirteenK_1584001, prime_thirteenK_25024350819790243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700821 : Nat.totient 15369469493336689477647700821 = 8738280940274603382506607360 := by
  rw [← show ((([(3, 1), (7, 1), (211, 1), (3299, 1), (1160494157, 1), (906007626637, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_7, prime_thirteenK_211, prime_thirteenK_3299, prime_thirteenK_1160494157, prime_thirteenK_906007626637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700822 : Nat.totient 15369469493336689477647700822 = 6906776103871282581047424000 := by
  rw [← show ((([(2, 1), (11, 1), (89, 1), (12301, 1), (24019, 1), (4553573, 1), (5834431507, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_11, prime_thirteenK_89, prime_thirteenK_12301, prime_thirteenK_24019, prime_thirteenK_4553573, prime_thirteenK_5834431507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700823 : Nat.totient 15369469493336689477647700823 = 14701228829181868659634723104 := by
  rw [← show ((([(23, 1), (5140117, 1), (130004395631094960253, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_23, prime_thirteenK_5140117, prime_thirteenK_130004395631094960253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700824 : Nat.totient 15369469493336689477647700824 = 5119443233670905812823249664 := by
  rw [← show ((([(2, 3), (3, 1), (1907, 1), (4987, 1), (67337590816601618489, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_1907, prime_thirteenK_4987, prime_thirteenK_67337590816601618489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700825 : Nat.totient 15369469493336689477647700825 = 12112059541017570215220873360 := by
  rw [← show ((([(5, 2), (67, 1), (9175802682589068344864299, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_5, prime_thirteenK_67, prime_thirteenK_9175802682589068344864299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700826 : Nat.totient 15369469493336689477647700826 = 7093601298814946944586473200 := by
  rw [← show ((([(2, 1), (13, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_13, prime_thirteenK_1222615931, prime_thirteenK_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700827 : Nat.totient 15369469493336689477647700827 = 10246299501368972883502204416 := by
  rw [← show ((([(3, 3), (759313, 1), (749677156672310144177, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_759313, prime_thirteenK_749677156672310144177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700828 : Nat.totient 15369469493336689477647700828 = 6586338860928139988757833904 := by
  rw [← show ((([(2, 2), (7, 1), (11423, 1), (48053018012958471872687, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_7, prime_thirteenK_11423, prime_thirteenK_48053018012958471872687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700829 : Nat.totient 15369469493336689477647700829 = 14645621071840733272837593600 := by
  rw [← show ((([(29, 1), (101, 1), (313, 1), (16764676135348824717077, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_29, prime_thirteenK_101, prime_thirteenK_313, prime_thirteenK_16764676135348824717077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700830 : Nat.totient 15369469493336689477647700830 = 4089556871749981270201222656 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (457, 1), (1121040809141990479770073, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_5, prime_thirteenK_457, prime_thirteenK_1121040809141990479770073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700831 : Nat.totient 15369469493336689477647700831 = 14870538397534880565550836000 := by
  rw [← show ((([(31, 1), (5683, 1), (28351, 1), (3077167559992740997, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_31, prime_thirteenK_5683, prime_thirteenK_28351, prime_thirteenK_3077167559992740997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700832 : Nat.totient 15369469493336689477647700832 = 7638718370132001087419307648 := by
  rw [← show ((([(2, 5), (167, 1), (9456603047, 1), (304128603975499, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_167, prime_thirteenK_9456603047, prime_thirteenK_304128603975499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700833 : Nat.totient 15369469493336689477647700833 = 9314826779049333877633858560 := by
  rw [← show ((([(3, 1), (11, 1), (3089857, 1), (46053307, 1), (3272997965299, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_11, prime_thirteenK_3089857, prime_thirteenK_46053307, prime_thirteenK_3272997965299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700834 : Nat.totient 15369469493336689477647700834 = 7208006572261495004975834880 := by
  rw [← show ((([(2, 1), (17, 2), (293, 1), (90753507406596180058621, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_17, prime_thirteenK_293, prime_thirteenK_90753507406596180058621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700835 : Nat.totient 15369469493336689477647700835 = 10538538048040355431451154432 := by
  rw [← show ((([(5, 1), (7, 1), (20029, 1), (18915877, 1), (1159057776105457, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_5, prime_thirteenK_7, prime_thirteenK_20029, prime_thirteenK_18915877, prime_thirteenK_1159057776105457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700836 : Nat.totient 15369469493336689477647700836 = 5118480403743092672834182656 := by
  rw [← show ((([(2, 2), (3, 2), (1097, 1), (873139, 1), (64502783, 1), (6910156909, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_1097, prime_thirteenK_873139, prime_thirteenK_64502783, prime_thirteenK_6910156909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700837 : Nat.totient 15369469493336689477647700837 = 14748761570152835994750738432 := by
  rw [← show ((([(37, 2), (73, 1), (31817, 1), (5082277, 1), (951075532889, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_37, prime_thirteenK_73, prime_thirteenK_31817, prime_thirteenK_5082277, prime_thirteenK_951075532889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700838 : Nat.totient 15369469493336689477647700838 = 7280275023159484489412068800 := by
  rw [← show ((([(2, 1), (19, 1), (404459723508860249411781601, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_19, prime_thirteenK_404459723508860249411781601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700839 : Nat.totient 15369469493336689477647700839 = 9458135072822578140090892800 := by
  rw [← show ((([(3, 1), (13, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_13, prime_thirteenK_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700840 : Nat.totient 15369469493336689477647700840 = 6147787797334675791059080320 := by
  rw [← show ((([(2, 3), (5, 1), (384236737333417236941192521, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_5, prime_thirteenK_384236737333417236941192521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700841 : Nat.totient 15369469493336689477647700841 = 14684732344550373318667958400 := by
  rw [← show ((([(41, 1), (79, 1), (131, 1), (2083, 1), (17389510759726903703, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_41, prime_thirteenK_79, prime_thirteenK_131, prime_thirteenK_2083, prime_thirteenK_17389510759726903703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700842 : Nat.totient 15369469493336689477647700842 = 4389958692182628636665641200 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (3331, 1), (109858826130696412328971, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_7, prime_thirteenK_3331, prime_thirteenK_109858826130696412328971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700843 : Nat.totient 15369469493336689477647700843 = 14806226255793556458530025216 := by
  rw [← show ((([(43, 1), (107, 1), (227, 1), (14715695298318302263009, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_43, prime_thirteenK_107, prime_thirteenK_227, prime_thirteenK_14715695298318302263009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700844 : Nat.totient 15369469493336689477647700844 = 6986122496905215177311778000 := by
  rw [← show ((([(2, 2), (11, 1), (105842008711, 1), (3300259784395591, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_11, prime_thirteenK_105842008711, prime_thirteenK_3300259784395591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700845 : Nat.totient 15369469493336689477647700845 = 8197050362328811022473919616 := by
  rw [← show ((([(3, 2), (5, 1), (240259949, 1), (1421559306659942309, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_5, prime_thirteenK_240259949, prime_thirteenK_1421559306659942309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700846 : Nat.totient 15369469493336689477647700846 = 7347985049081782739166480640 := by
  rw [← show ((([(2, 1), (23, 1), (3203, 1), (21911, 1), (14457413, 1), (329299688969, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_23, prime_thirteenK_3203, prime_thirteenK_21911, prime_thirteenK_14457413, prime_thirteenK_329299688969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700847 : Nat.totient 15369469493336689477647700847 = 15011571370279220445198224448 := by
  rw [← show ((([(47, 1), (487, 1), (118535279, 1), (5664798049611737, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_47, prime_thirteenK_487, prime_thirteenK_118535279, prime_thirteenK_5664798049611737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700848 : Nat.totient 15369469493336689477647700848 = 5119551097020733267310727168 := by
  rw [← show ((([(2, 4), (3, 1), (2383, 1), (3719, 1), (65713, 1), (9441539, 1), (58233559, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_2383, prime_thirteenK_3719, prime_thirteenK_65713, prime_thirteenK_9441539, prime_thirteenK_58233559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700849 : Nat.totient 15369469493336689477647700849 = 13085334521995466383390273536 := by
  rw [← show ((([(7, 2), (149, 1), (161717, 1), (22420633, 1), (580594587409, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_7, prime_thirteenK_149, prime_thirteenK_161717, prime_thirteenK_22420633, prime_thirteenK_580594587409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700850 : Nat.totient 15369469493336689477647700850 = 6133141335225942969291360000 := by
  rw [← show ((([(2, 1), (5, 2), (431, 1), (16069, 1), (8132653, 1), (5457459350351, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_5, prime_thirteenK_431, prime_thirteenK_16069, prime_thirteenK_8132653, prime_thirteenK_5457459350351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700851 : Nat.totient 15369469493336689477647700851 = 9555071657055070387920814080 := by
  rw [← show ((([(3, 1), (17, 1), (179, 1), (277, 1), (427681, 1), (14211369920432687, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_17, prime_thirteenK_179, prime_thirteenK_277, prime_thirteenK_427681, prime_thirteenK_14211369920432687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700852 : Nat.totient 15369469493336689477647700852 = 7093600965708594895951147008 := by
  rw [← show ((([(2, 2), (13, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_13, prime_thirteenK_20930737, prime_thirteenK_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700853 : Nat.totient 15369469493336689477647700853 = 14941011590378221996651947840 := by
  rw [← show ((([(53, 1), (109, 1), (120431, 1), (22091144538306559019, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_53, prime_thirteenK_109, prime_thirteenK_120431, prime_thirteenK_22091144538306559019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700854 : Nat.totient 15369469493336689477647700854 = 5061431720407559801574403008 := by
  rw [← show ((([(2, 1), (3, 4), (83, 1), (17478173717, 1), (65398790854597, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_83, prime_thirteenK_17478173717, prime_thirteenK_65398790854597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700855 : Nat.totient 15369469493336689477647700855 = 11177787181982150607772876800 := by
  rw [← show ((([(5, 1), (11, 1), (1547593, 1), (7027961, 1), (25692720254657, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_5, prime_thirteenK_11, prime_thirteenK_1547593, prime_thirteenK_7027961, prime_thirteenK_25692720254657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700856 : Nat.totient 15369469493336689477647700856 = 6586915497144295490420443200 := by
  rw [← show ((([(2, 3), (7, 1), (274454812381012312100851801, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_7, prime_thirteenK_274454812381012312100851801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700857 : Nat.totient 15369469493336689477647700857 = 9569159725670138235722048640 := by
  rw [← show ((([(3, 1), (19, 1), (71, 1), (8287, 1), (458277287644781321513, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_19, prime_thirteenK_71, prime_thirteenK_8287, prime_thirteenK_458277287644781321513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700858 : Nat.totient 15369469493336689477647700858 = 7411188127195622709998682624 := by
  rw [← show ((([(2, 1), (29, 1), (877, 1), (77689, 1), (3889302824472379117, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_29, prime_thirteenK_877, prime_thirteenK_77689, prime_thirteenK_3889302824472379117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700859 : Nat.totient 15369469493336689477647700859 = 15108234386721241693039531776 := by
  rw [← show ((([(59, 1), (20543, 1), (105309793, 1), (120413239471199, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_59, prime_thirteenK_20543, prime_thirteenK_105309793, prime_thirteenK_120413239471199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700860 : Nat.totient 15369469493336689477647700860 = 4098393263656644646948081152 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (31223, 1), (6132143, 1), (1337890974223129, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_5, prime_thirteenK_31223, prime_thirteenK_6132143, prime_thirteenK_1337890974223129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700861 : Nat.totient 15369469493336689477647700861 = 15024739613713387502434254720 := by
  rw [← show ((([(61, 1), (163, 1), (580169, 1), (2664323272382311283, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_61, prime_thirteenK_163, prime_thirteenK_580169, prime_thirteenK_2664323272382311283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700862 : Nat.totient 15369469493336689477647700862 = 7436840077414930480167603960 := by
  rw [← show ((([(2, 1), (31, 1), (1237167199903, 1), (200372810778367, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_31, prime_thirteenK_1237167199903, prime_thirteenK_200372810778367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700863 : Nat.totient 15369469493336689477647700863 = 8781541689493347863506329600 := by
  rw [← show ((([(3, 2), (7, 1), (15809, 1), (19231, 1), (82882231, 1), (9681677849, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_7, prime_thirteenK_15809, prime_thirteenK_19231, prime_thirteenK_82882231, prime_thirteenK_9681677849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700864 : Nat.totient 15369469493336689477647700864 = 7684124845276007150908354560 := by
  rw [← show ((([(2, 7), (12697, 1), (1648531, 1), (5736548500147109, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_12697, prime_thirteenK_1648531, prime_thirteenK_5736548500147109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700865 : Nat.totient 15369469493336689477647700865 = 11349762069258819981887023296 := by
  rw [← show ((([(5, 1), (13, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_5, prime_thirteenK_13, prime_thirteenK_626080687, prime_thirteenK_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700866 : Nat.totient 15369469493336689477647700866 = 4657414997043232337944536000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 2), (4967477161, 1), (4261734374713931, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_11, prime_thirteenK_4967477161, prime_thirteenK_4261734374713931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700867 : Nat.totient 15369469493336689477647700867 = 15369469318004939463364903200 := by
  rw [← show ((([(89131981, 1), (6677766077, 1), (25822252091, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_89131981, prime_thirteenK_6677766077, prime_thirteenK_25822252091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700868 : Nat.totient 15369469493336689477647700868 = 7212983919937462219995575424 := by
  rw [← show ((([(2, 2), (17, 1), (367, 1), (615862698082092061133503, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_17, prime_thirteenK_367, prime_thirteenK_615862698082092061133503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700869 : Nat.totient 15369469493336689477647700869 = 9775851827172833303260763712 := by
  rw [← show ((([(3, 1), (23, 1), (607, 1), (1109, 1), (330894500568270950627, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_23, prime_thirteenK_607, prime_thirteenK_1109, prime_thirteenK_330894500568270950627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700870 : Nat.totient 15369469493336689477647700870 = 5242222450717453747751602176 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (193, 2), (785903, 1), (7500276474838703, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_5, prime_thirteenK_7, prime_thirteenK_193, prime_thirteenK_785903, prime_thirteenK_7500276474838703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700871 : Nat.totient 15369469493336689477647700871 = 15369469493336689477647700870 := by
  rw [← show ((([(15369469493336689477647700871, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_15369469493336689477647700871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700872 : Nat.totient 15369469493336689477647700872 = 5121107986509033335723971584 := by
  rw [← show ((([(2, 3), (3, 2), (4889, 1), (5119, 1), (562403069, 1), (15166086619, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_4889, prime_thirteenK_5119, prime_thirteenK_562403069, prime_thirteenK_15166086619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700873 : Nat.totient 15369469493336689477647700873 = 15369469493336689477647700872 := by
  rw [← show ((([(15369469493336689477647700873, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_15369469493336689477647700873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700874 : Nat.totient 15369469493336689477647700874 = 7399955946047072842417471488 := by
  rw [← show ((([(2, 1), (37, 1), (97, 1), (19050289, 1), (112396776185790097, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_37, prime_thirteenK_97, prime_thirteenK_19050289, prime_thirteenK_112396776185790097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700875 : Nat.totient 15369469493336689477647700875 = 8191054017224254699425919200 := by
  rw [← show ((([(3, 1), (5, 3), (1367, 1), (29981896109898443262907, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_5, prime_thirteenK_1367, prime_thirteenK_29981896109898443262907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700876 : Nat.totient 15369469493336689477647700876 = 7279928656775586136278936144 := by
  rw [← show ((([(2, 2), (19, 1), (21019, 1), (9621288441620920343779, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_19, prime_thirteenK_21019, prime_thirteenK_9621288441620920343779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700877 : Nat.totient 15369469493336689477647700877 = 11976209994081515245735461120 := by
  rw [← show ((([(7, 1), (11, 1), (16489485193, 1), (12104895791300857, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_7, prime_thirteenK_11, prime_thirteenK_16489485193, prime_thirteenK_12104895791300857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700878 : Nat.totient 15369469493336689477647700878 = 4717400485682981134329322752 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_13, prime_thirteenK_409, prime_thirteenK_45127, prime_thirteenK_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700879 : Nat.totient 15369469493336689477647700879 = 15369469493336420567493763584 := by
  rw [← show ((([(82409921292943, 1), (186500232644353, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_82409921292943, prime_thirteenK_186500232644353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700880 : Nat.totient 15369469493336689477647700880 = 6147787797334675791059080320 := by
  rw [← show ((([(2, 4), (5, 1), (192118368666708618470596261, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_5, prime_thirteenK_192118368666708618470596261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700881 : Nat.totient 15369469493336689477647700881 = 10246312995546024165081378240 := by
  rw [← show ((([(3, 3), (871794576241, 1), (652951539706483, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_871794576241, prime_thirteenK_652951539706483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700882 : Nat.totient 15369469493336689477647700882 = 7431579921989355301945589760 := by
  rw [← show ((([(2, 1), (41, 1), (173, 1), (359, 1), (4583, 1), (33642613, 1), (19573338017, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_41, prime_thirteenK_173, prime_thirteenK_359, prime_thirteenK_4583, prime_thirteenK_33642613, prime_thirteenK_19573338017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700883 : Nat.totient 15369469493336689477647700883 = 15369469291252968820129069920 := by
  rw [← show ((([(76054961, 1), (202083720657442576003, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_76054961, prime_thirteenK_202083720657442576003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700884 : Nat.totient 15369469493336689477647700884 = 4388431063528135516016170368 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (1543, 1), (272119617229, 1), (435766473283, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_7, prime_thirteenK_1543, prime_thirteenK_272119617229, prime_thirteenK_435766473283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700885 : Nat.totient 15369469493336689477647700885 = 11572306442041742665522974720 := by
  rw [← show ((([(5, 1), (17, 1), (180817288156902229148796481, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_5, prime_thirteenK_17, prime_thirteenK_180817288156902229148796481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700886 : Nat.totient 15369469493336689477647700886 = 7438082609284049721444050304 := by
  rw [← show ((([(2, 1), (43, 1), (113, 1), (4919, 1), (321517902499116882583, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_43, prime_thirteenK_113, prime_thirteenK_4919, prime_thirteenK_321517902499116882583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700887 : Nat.totient 15369469493336689477647700887 = 9892991810547156778506772992 := by
  rw [← show ((([(3, 1), (29, 1), (209451817, 1), (843442522577531353, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_29, prime_thirteenK_209451817, prime_thirteenK_843442522577531353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700888 : Nat.totient 15369469493336689477647700888 = 6986103694334792434618041600 := by
  rw [← show ((([(2, 3), (11, 1), (372023, 1), (292379671, 1), (1605680900297, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_11, prime_thirteenK_372023, prime_thirteenK_292379671, prime_thirteenK_1605680900297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700889 : Nat.totient 15369469493336689477647700889 = 15369469493336689477647700888 := by
  rw [← show ((([(15369469493336689477647700889, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_15369469493336689477647700889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700890 : Nat.totient 15369469493336689477647700890 = 4083328211050169959896268800 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (389, 1), (881, 1), (196661, 1), (2533801651658729, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_5, prime_thirteenK_389, prime_thirteenK_881, prime_thirteenK_196661, prime_thirteenK_2533801651658729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700891 : Nat.totient 15369469493336689477647700891 = 12134080941612013621283034240 := by
  rw [← show ((([(7, 1), (13, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_7, prime_thirteenK_13, prime_thirteenK_461, prime_thirteenK_13492702567, prime_thirteenK_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700892 : Nat.totient 15369469493336689477647700892 = 7240532040259634346574417920 := by
  rw [← show ((([(2, 2), (23, 1), (67, 1), (31271, 1), (51913, 1), (3492397, 1), (439799513, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_23, prime_thirteenK_67, prime_thirteenK_31271, prime_thirteenK_51913, prime_thirteenK_3492397, prime_thirteenK_439799513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700893 : Nat.totient 15369469493336689477647700893 = 9915786769894638372675936000 := by
  rw [← show ((([(3, 1), (31, 1), (165263112831577306211265601, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_3, prime_thirteenK_31, prime_thirteenK_165263112831577306211265601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700894 : Nat.totient 15369469493336689477647700894 = 7521229751937119911921333432 := by
  rw [← show ((([(2, 1), (47, 1), (62027081687, 1), (2636025912601223, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_47, prime_thirteenK_62027081687, prime_thirteenK_2636025912601223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700895 : Nat.totient 15369469493336689477647700895 = 11644307919269770722192466848 := by
  rw [← show ((([(5, 1), (19, 1), (2819, 1), (57390524797284178703339, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_5, prime_thirteenK_19, prime_thirteenK_2819, prime_thirteenK_57390524797284178703339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700896 : Nat.totient 15369469493336689477647700896 = 5123156497777676072206627328 := by
  rw [← show ((([(2, 5), (3, 1), (4802648953049, 1), (33335486753399, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_3, prime_thirteenK_4802648953049, prime_thirteenK_33335486753399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700897 : Nat.totient 15369469493336689477647700897 = 15305370339533156546403678400 := by
  rw [← show ((([(269, 1), (2687, 1), (12101, 1), (1757185738698779999, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_269, prime_thirteenK_2687, prime_thirteenK_12101, prime_thirteenK_1757185738698779999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirteenK_15369469493336689477647700898 : Nat.totient 15369469493336689477647700898 = 6575687547688871008358169600 := by
  rw [← show ((([(2, 1), (7, 2), (587, 1), (1000981, 1), (116997143, 1), (2281358881, 1)] : List FactorBlock).map factorBlockValue).prod) = 15369469493336689477647700898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirteenK_2, prime_thirteenK_7, prime_thirteenK_587, prime_thirteenK_1000981, prime_thirteenK_116997143, prime_thirteenK_2281358881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirteenK : certifiedKill 1 15369469493336689477647700799 98 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirteenK_15369469493336689477647700800, phi_thirteenK_15369469493336689477647700801, phi_thirteenK_15369469493336689477647700802,
    phi_thirteenK_15369469493336689477647700803, phi_thirteenK_15369469493336689477647700804, phi_thirteenK_15369469493336689477647700805,
    phi_thirteenK_15369469493336689477647700806, phi_thirteenK_15369469493336689477647700807, phi_thirteenK_15369469493336689477647700808,
    phi_thirteenK_15369469493336689477647700809, phi_thirteenK_15369469493336689477647700810, phi_thirteenK_15369469493336689477647700811,
    phi_thirteenK_15369469493336689477647700812, phi_thirteenK_15369469493336689477647700813, phi_thirteenK_15369469493336689477647700814,
    phi_thirteenK_15369469493336689477647700815, phi_thirteenK_15369469493336689477647700816, phi_thirteenK_15369469493336689477647700817,
    phi_thirteenK_15369469493336689477647700818, phi_thirteenK_15369469493336689477647700819, phi_thirteenK_15369469493336689477647700820,
    phi_thirteenK_15369469493336689477647700821, phi_thirteenK_15369469493336689477647700822, phi_thirteenK_15369469493336689477647700823,
    phi_thirteenK_15369469493336689477647700824, phi_thirteenK_15369469493336689477647700825, phi_thirteenK_15369469493336689477647700826,
    phi_thirteenK_15369469493336689477647700827, phi_thirteenK_15369469493336689477647700828, phi_thirteenK_15369469493336689477647700829,
    phi_thirteenK_15369469493336689477647700830, phi_thirteenK_15369469493336689477647700831, phi_thirteenK_15369469493336689477647700832,
    phi_thirteenK_15369469493336689477647700833, phi_thirteenK_15369469493336689477647700834, phi_thirteenK_15369469493336689477647700835,
    phi_thirteenK_15369469493336689477647700836, phi_thirteenK_15369469493336689477647700837, phi_thirteenK_15369469493336689477647700838,
    phi_thirteenK_15369469493336689477647700839, phi_thirteenK_15369469493336689477647700840, phi_thirteenK_15369469493336689477647700841,
    phi_thirteenK_15369469493336689477647700842, phi_thirteenK_15369469493336689477647700843, phi_thirteenK_15369469493336689477647700844,
    phi_thirteenK_15369469493336689477647700845, phi_thirteenK_15369469493336689477647700846, phi_thirteenK_15369469493336689477647700847,
    phi_thirteenK_15369469493336689477647700848, phi_thirteenK_15369469493336689477647700849, phi_thirteenK_15369469493336689477647700850,
    phi_thirteenK_15369469493336689477647700851, phi_thirteenK_15369469493336689477647700852, phi_thirteenK_15369469493336689477647700853,
    phi_thirteenK_15369469493336689477647700854, phi_thirteenK_15369469493336689477647700855, phi_thirteenK_15369469493336689477647700856,
    phi_thirteenK_15369469493336689477647700857, phi_thirteenK_15369469493336689477647700858, phi_thirteenK_15369469493336689477647700859,
    phi_thirteenK_15369469493336689477647700860, phi_thirteenK_15369469493336689477647700861, phi_thirteenK_15369469493336689477647700862,
    phi_thirteenK_15369469493336689477647700863, phi_thirteenK_15369469493336689477647700864, phi_thirteenK_15369469493336689477647700865,
    phi_thirteenK_15369469493336689477647700866, phi_thirteenK_15369469493336689477647700867, phi_thirteenK_15369469493336689477647700868,
    phi_thirteenK_15369469493336689477647700869, phi_thirteenK_15369469493336689477647700870, phi_thirteenK_15369469493336689477647700871,
    phi_thirteenK_15369469493336689477647700872, phi_thirteenK_15369469493336689477647700873, phi_thirteenK_15369469493336689477647700874,
    phi_thirteenK_15369469493336689477647700875, phi_thirteenK_15369469493336689477647700876, phi_thirteenK_15369469493336689477647700877,
    phi_thirteenK_15369469493336689477647700878, phi_thirteenK_15369469493336689477647700879, phi_thirteenK_15369469493336689477647700880,
    phi_thirteenK_15369469493336689477647700881, phi_thirteenK_15369469493336689477647700882, phi_thirteenK_15369469493336689477647700883,
    phi_thirteenK_15369469493336689477647700884, phi_thirteenK_15369469493336689477647700885, phi_thirteenK_15369469493336689477647700886,
    phi_thirteenK_15369469493336689477647700887, phi_thirteenK_15369469493336689477647700888, phi_thirteenK_15369469493336689477647700889,
    phi_thirteenK_15369469493336689477647700890, phi_thirteenK_15369469493336689477647700891, phi_thirteenK_15369469493336689477647700892,
    phi_thirteenK_15369469493336689477647700893, phi_thirteenK_15369469493336689477647700894, phi_thirteenK_15369469493336689477647700895,
    phi_thirteenK_15369469493336689477647700896, phi_thirteenK_15369469493336689477647700897, phi_thirteenK_15369469493336689477647700898]

end TotientTailPeriodKiller
end Erdos249257
