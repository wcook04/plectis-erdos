import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFifteenDIFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFifteenDIFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFifteenDIFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFifteenDIFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFifteenDIFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFifteenDIFastPow a n * oneHundredFifteenDIFastPow a n * a else oneHundredFifteenDIFastPow a n * oneHundredFifteenDIFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFifteenDI_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFifteenDI_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFifteenDI_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFifteenDI_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFifteenDI_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFifteenDI_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFifteenDI_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFifteenDI_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFifteenDI_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFifteenDI_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFifteenDI_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFifteenDI_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFifteenDI_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFifteenDI_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFifteenDI_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFifteenDI_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFifteenDI_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFifteenDI_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFifteenDI_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFifteenDI_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFifteenDI_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFifteenDI_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFifteenDI_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFifteenDI_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFifteenDI_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFifteenDI_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFifteenDI_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFifteenDI_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFifteenDI_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFifteenDI_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFifteenDI_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFifteenDI_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFifteenDI_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFifteenDI_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFifteenDI_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFifteenDI_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFifteenDI_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFifteenDI_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFifteenDI_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFifteenDI_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFifteenDI_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFifteenDI_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFifteenDI_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFifteenDI_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFifteenDI_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFifteenDI_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFifteenDI_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFifteenDI_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFifteenDI_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFifteenDI_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFifteenDI_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFifteenDI_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFifteenDI_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFifteenDI_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFifteenDI_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFifteenDI_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFifteenDI_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFifteenDI_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFifteenDI_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFifteenDI_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFifteenDI_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFifteenDI_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFifteenDI_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFifteenDI_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFifteenDI_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFifteenDI_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFifteenDI_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFifteenDI_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFifteenDI_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFifteenDI_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFifteenDI_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredFifteenDI_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFifteenDI_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFifteenDI_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFifteenDI_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFifteenDI_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFifteenDI_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredFifteenDI_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFifteenDI_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFifteenDI_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFifteenDI_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFifteenDI_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredFifteenDI_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredFifteenDI_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFifteenDI_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredFifteenDI_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFifteenDI_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredFifteenDI_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFifteenDI_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredFifteenDI_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredFifteenDI_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredFifteenDI_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFifteenDI_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredFifteenDI_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFifteenDI_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredFifteenDI_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFifteenDI_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredFifteenDI_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFifteenDI_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFifteenDI_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredFifteenDI_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredFifteenDI_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFifteenDI_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredFifteenDI_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredFifteenDI_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredFifteenDI_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredFifteenDI_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredFifteenDI_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredFifteenDI_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredFifteenDI_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredFifteenDI_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredFifteenDI_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFifteenDI_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredFifteenDI_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredFifteenDI_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredFifteenDI_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredFifteenDI_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredFifteenDI_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredFifteenDI_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredFifteenDI_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFifteenDI_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredFifteenDI_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredFifteenDI_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredFifteenDI_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredFifteenDI_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredFifteenDI_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredFifteenDI_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredFifteenDI_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredFifteenDI_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredFifteenDI_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredFifteenDI_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredFifteenDI_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredFifteenDI_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredFifteenDI_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredFifteenDI_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredFifteenDI_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredFifteenDI_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredFifteenDI_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_oneHundredFifteenDI_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredFifteenDI_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_oneHundredFifteenDI_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_oneHundredFifteenDI_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredFifteenDI_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredFifteenDI_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_oneHundredFifteenDI_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_oneHundredFifteenDI_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredFifteenDI_2333 : Nat.Prime 2333 := by norm_num

private theorem prime_oneHundredFifteenDI_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredFifteenDI_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_oneHundredFifteenDI_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_oneHundredFifteenDI_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredFifteenDI_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredFifteenDI_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredFifteenDI_2749 : Nat.Prime 2749 := by norm_num

private theorem prime_oneHundredFifteenDI_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_oneHundredFifteenDI_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredFifteenDI_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_oneHundredFifteenDI_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredFifteenDI_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_oneHundredFifteenDI_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_oneHundredFifteenDI_3121 : Nat.Prime 3121 := by norm_num

private theorem prime_oneHundredFifteenDI_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_oneHundredFifteenDI_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredFifteenDI_3527 : Nat.Prime 3527 := by norm_num

private theorem prime_oneHundredFifteenDI_3907 : Nat.Prime 3907 := by norm_num

private theorem prime_oneHundredFifteenDI_3917 : Nat.Prime 3917 := by norm_num

private theorem prime_oneHundredFifteenDI_3989 : Nat.Prime 3989 := by norm_num

private theorem prime_oneHundredFifteenDI_4127 : Nat.Prime 4127 := by norm_num

private theorem prime_oneHundredFifteenDI_4139 : Nat.Prime 4139 := by norm_num

private theorem prime_oneHundredFifteenDI_4231 : Nat.Prime 4231 := by norm_num

private theorem prime_oneHundredFifteenDI_4441 : Nat.Prime 4441 := by norm_num

private theorem prime_oneHundredFifteenDI_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_oneHundredFifteenDI_5023 : Nat.Prime 5023 := by norm_num

private theorem prime_oneHundredFifteenDI_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredFifteenDI_5197 : Nat.Prime 5197 := by norm_num

private theorem prime_oneHundredFifteenDI_5237 : Nat.Prime 5237 := by norm_num

private theorem prime_oneHundredFifteenDI_5393 : Nat.Prime 5393 := by norm_num

private theorem prime_oneHundredFifteenDI_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_oneHundredFifteenDI_5879 : Nat.Prime 5879 := by norm_num

private theorem prime_oneHundredFifteenDI_6173 : Nat.Prime 6173 := by norm_num

private theorem prime_oneHundredFifteenDI_6221 : Nat.Prime 6221 := by norm_num

private theorem prime_oneHundredFifteenDI_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_oneHundredFifteenDI_6361 : Nat.Prime 6361 := by norm_num

private theorem prime_oneHundredFifteenDI_6367 : Nat.Prime 6367 := by norm_num

private theorem prime_oneHundredFifteenDI_6653 : Nat.Prime 6653 := by norm_num

private theorem prime_oneHundredFifteenDI_6733 : Nat.Prime 6733 := by norm_num

private theorem prime_oneHundredFifteenDI_6793 : Nat.Prime 6793 := by norm_num

private theorem prime_oneHundredFifteenDI_6841 : Nat.Prime 6841 := by norm_num

private theorem prime_oneHundredFifteenDI_7537 : Nat.Prime 7537 := by norm_num

private theorem prime_oneHundredFifteenDI_7549 : Nat.Prime 7549 := by norm_num

private theorem prime_oneHundredFifteenDI_7723 : Nat.Prime 7723 := by norm_num

private theorem prime_oneHundredFifteenDI_7823 : Nat.Prime 7823 := by norm_num

private theorem prime_oneHundredFifteenDI_8053 : Nat.Prime 8053 := by norm_num

private theorem prime_oneHundredFifteenDI_8369 : Nat.Prime 8369 := by norm_num

private theorem prime_oneHundredFifteenDI_8563 : Nat.Prime 8563 := by norm_num

private theorem prime_oneHundredFifteenDI_8663 : Nat.Prime 8663 := by norm_num

private theorem prime_oneHundredFifteenDI_9043 : Nat.Prime 9043 := by norm_num

private theorem prime_oneHundredFifteenDI_9103 : Nat.Prime 9103 := by norm_num

private theorem prime_oneHundredFifteenDI_9133 : Nat.Prime 9133 := by norm_num

private theorem prime_oneHundredFifteenDI_9677 : Nat.Prime 9677 := by norm_num

private theorem prime_oneHundredFifteenDI_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredFifteenDI_9851 : Nat.Prime 9851 := by norm_num

private theorem prime_oneHundredFifteenDI_10067 : Nat.Prime 10067 := by norm_num

private theorem prime_oneHundredFifteenDI_10111 : Nat.Prime 10111 := by norm_num

private theorem prime_oneHundredFifteenDI_10211 : Nat.Prime 10211 := by norm_num

private theorem prime_oneHundredFifteenDI_10597 : Nat.Prime 10597 := by norm_num

private theorem prime_oneHundredFifteenDI_10979 : Nat.Prime 10979 := by norm_num

private theorem prime_oneHundredFifteenDI_11171 : Nat.Prime 11171 := by norm_num

private theorem prime_oneHundredFifteenDI_11239 : Nat.Prime 11239 := by norm_num

private theorem prime_oneHundredFifteenDI_11443 : Nat.Prime 11443 := by norm_num

private theorem prime_oneHundredFifteenDI_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredFifteenDI_11743 : Nat.Prime 11743 := by norm_num

private theorem prime_oneHundredFifteenDI_12281 : Nat.Prime 12281 := by norm_num

private theorem prime_oneHundredFifteenDI_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredFifteenDI_12791 : Nat.Prime 12791 := by norm_num

private theorem prime_oneHundredFifteenDI_13063 : Nat.Prime 13063 := by norm_num

private theorem prime_oneHundredFifteenDI_13093 : Nat.Prime 13093 := by norm_num

private theorem prime_oneHundredFifteenDI_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredFifteenDI_15101 : Nat.Prime 15101 := by norm_num

private theorem prime_oneHundredFifteenDI_15149 : Nat.Prime 15149 := by norm_num

private theorem prime_oneHundredFifteenDI_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredFifteenDI_15643 : Nat.Prime 15643 := by norm_num

private theorem prime_oneHundredFifteenDI_15787 : Nat.Prime 15787 := by norm_num

private theorem prime_oneHundredFifteenDI_16411 : Nat.Prime 16411 := by norm_num

private theorem prime_oneHundredFifteenDI_16573 : Nat.Prime 16573 := by norm_num

private theorem prime_oneHundredFifteenDI_16963 : Nat.Prime 16963 := by norm_num

private theorem prime_oneHundredFifteenDI_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFifteenDI_17747 : Nat.Prime 17747 := by norm_num

private theorem prime_oneHundredFifteenDI_18731 : Nat.Prime 18731 := by norm_num

private theorem prime_oneHundredFifteenDI_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFifteenDI_20939 : Nat.Prime 20939 := by norm_num

private theorem prime_oneHundredFifteenDI_21701 : Nat.Prime 21701 := by norm_num

private theorem prime_oneHundredFifteenDI_23021 : Nat.Prime 23021 := by norm_num

private theorem prime_oneHundredFifteenDI_23173 : Nat.Prime 23173 := by norm_num

private theorem prime_oneHundredFifteenDI_23291 : Nat.Prime 23291 := by norm_num

private theorem prime_oneHundredFifteenDI_24683 : Nat.Prime 24683 := by norm_num

private theorem prime_oneHundredFifteenDI_24943 : Nat.Prime 24943 := by norm_num

private theorem prime_oneHundredFifteenDI_25841 : Nat.Prime 25841 := by norm_num

private theorem prime_oneHundredFifteenDI_26573 : Nat.Prime 26573 := by norm_num

private theorem prime_oneHundredFifteenDI_28729 : Nat.Prime 28729 := by norm_num

private theorem prime_oneHundredFifteenDI_28901 : Nat.Prime 28901 := by norm_num

private theorem prime_oneHundredFifteenDI_29641 : Nat.Prime 29641 := by norm_num

private theorem prime_oneHundredFifteenDI_30671 : Nat.Prime 30671 := by norm_num

private theorem prime_oneHundredFifteenDI_30937 : Nat.Prime 30937 := by norm_num

private theorem prime_oneHundredFifteenDI_31153 : Nat.Prime 31153 := by norm_num

private theorem prime_oneHundredFifteenDI_31321 : Nat.Prime 31321 := by norm_num

private theorem prime_oneHundredFifteenDI_31847 : Nat.Prime 31847 := by norm_num

private theorem prime_oneHundredFifteenDI_32089 : Nat.Prime 32089 := by norm_num

private theorem prime_oneHundredFifteenDI_35267 : Nat.Prime 35267 := by norm_num

private theorem prime_oneHundredFifteenDI_38603 : Nat.Prime 38603 := by norm_num

private theorem prime_oneHundredFifteenDI_39371 : Nat.Prime 39371 := by norm_num

private theorem prime_oneHundredFifteenDI_41603 : Nat.Prime 41603 := by norm_num

private theorem prime_oneHundredFifteenDI_42929 : Nat.Prime 42929 := by norm_num

private theorem prime_oneHundredFifteenDI_43669 : Nat.Prime 43669 := by norm_num

private theorem prime_oneHundredFifteenDI_43793 : Nat.Prime 43793 := by norm_num

private theorem prime_oneHundredFifteenDI_45989 : Nat.Prime 45989 := by norm_num

private theorem prime_oneHundredFifteenDI_47947 : Nat.Prime 47947 := by norm_num

private theorem prime_oneHundredFifteenDI_49331 : Nat.Prime 49331 := by norm_num

private theorem prime_oneHundredFifteenDI_57077 : Nat.Prime 57077 := by norm_num

private theorem prime_oneHundredFifteenDI_57139 : Nat.Prime 57139 := by norm_num

private theorem prime_oneHundredFifteenDI_60601 : Nat.Prime 60601 := by norm_num

private theorem prime_oneHundredFifteenDI_63029 : Nat.Prime 63029 := by norm_num

private theorem prime_oneHundredFifteenDI_63533 : Nat.Prime 63533 := by norm_num

private theorem prime_oneHundredFifteenDI_64709 : Nat.Prime 64709 := by norm_num

private theorem prime_oneHundredFifteenDI_68813 : Nat.Prime 68813 := by norm_num

private theorem prime_oneHundredFifteenDI_74759 : Nat.Prime 74759 := by norm_num

private theorem prime_oneHundredFifteenDI_75347 : Nat.Prime 75347 := by norm_num

private theorem prime_oneHundredFifteenDI_79283 : Nat.Prime 79283 := by norm_num

private theorem prime_oneHundredFifteenDI_82013 : Nat.Prime 82013 := by norm_num

private theorem prime_oneHundredFifteenDI_87121 : Nat.Prime 87121 := by norm_num

private theorem prime_oneHundredFifteenDI_87751 : Nat.Prime 87751 := by norm_num

private theorem prime_oneHundredFifteenDI_94309 : Nat.Prime 94309 := by norm_num

private theorem prime_oneHundredFifteenDI_97381 : Nat.Prime 97381 := by norm_num

private theorem prime_oneHundredFifteenDI_100799 : Nat.Prime 100799 := by norm_num

private theorem prime_oneHundredFifteenDI_102983 : Nat.Prime 102983 := by norm_num

private theorem prime_oneHundredFifteenDI_109279 : Nat.Prime 109279 := by norm_num

private theorem prime_oneHundredFifteenDI_111053 : Nat.Prime 111053 := by norm_num

private theorem prime_oneHundredFifteenDI_114691 : Nat.Prime 114691 := by norm_num

private theorem prime_oneHundredFifteenDI_115399 : Nat.Prime 115399 := by norm_num

private theorem prime_oneHundredFifteenDI_133963 : Nat.Prime 133963 := by norm_num

private theorem prime_oneHundredFifteenDI_136733 : Nat.Prime 136733 := by norm_num

private theorem prime_oneHundredFifteenDI_136949 : Nat.Prime 136949 := by norm_num

private theorem prime_oneHundredFifteenDI_141277 : Nat.Prime 141277 := by norm_num

private theorem prime_oneHundredFifteenDI_153437 : Nat.Prime 153437 := by norm_num

private theorem prime_oneHundredFifteenDI_153623 : Nat.Prime 153623 := by norm_num

private theorem prime_oneHundredFifteenDI_156109 : Nat.Prime 156109 := by norm_num

private theorem prime_oneHundredFifteenDI_157627 : Nat.Prime 157627 := by norm_num

private theorem prime_oneHundredFifteenDI_158881 : Nat.Prime 158881 := by norm_num

private theorem prime_oneHundredFifteenDI_160813 : Nat.Prime 160813 := by norm_num

private theorem prime_oneHundredFifteenDI_162787 : Nat.Prime 162787 := by norm_num

private theorem prime_oneHundredFifteenDI_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFifteenDI_174331 : Nat.Prime 174331 := by norm_num

private theorem prime_oneHundredFifteenDI_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredFifteenDI_192037 : Nat.Prime 192037 := by norm_num

private theorem prime_oneHundredFifteenDI_193619 : Nat.Prime 193619 := by norm_num

private theorem prime_oneHundredFifteenDI_195469 : Nat.Prime 195469 := by norm_num

private theorem prime_oneHundredFifteenDI_204613 : Nat.Prime 204613 := by norm_num

private theorem prime_oneHundredFifteenDI_222659 : Nat.Prime 222659 := by norm_num

private theorem prime_oneHundredFifteenDI_245981 : Nat.Prime 245981 := by norm_num

private theorem prime_oneHundredFifteenDI_248351 : Nat.Prime 248351 := by norm_num

private theorem prime_oneHundredFifteenDI_260171 : Nat.Prime 260171 := by norm_num

private theorem prime_oneHundredFifteenDI_270859 : Nat.Prime 270859 := by norm_num

private theorem prime_oneHundredFifteenDI_276239 : Nat.Prime 276239 := by norm_num

private theorem prime_oneHundredFifteenDI_282589 : Nat.Prime 282589 := by norm_num

private theorem prime_oneHundredFifteenDI_286073 : Nat.Prime 286073 := by norm_num

private theorem prime_oneHundredFifteenDI_301657 : Nat.Prime 301657 := by norm_num

private theorem prime_oneHundredFifteenDI_311791 : Nat.Prime 311791 := by norm_num

private theorem prime_oneHundredFifteenDI_346441 : Nat.Prime 346441 := by norm_num

private theorem prime_oneHundredFifteenDI_351361 : Nat.Prime 351361 := by norm_num

private theorem prime_oneHundredFifteenDI_356137 : Nat.Prime 356137 := by norm_num

private theorem prime_oneHundredFifteenDI_383419 : Nat.Prime 383419 := by norm_num

private theorem prime_oneHundredFifteenDI_392443 : Nat.Prime 392443 := by norm_num

private theorem prime_oneHundredFifteenDI_416833 : Nat.Prime 416833 := by norm_num

private theorem prime_oneHundredFifteenDI_432499 : Nat.Prime 432499 := by norm_num

private theorem prime_oneHundredFifteenDI_445699 : Nat.Prime 445699 := by norm_num

private theorem prime_oneHundredFifteenDI_463339 : Nat.Prime 463339 := by norm_num

private theorem prime_oneHundredFifteenDI_463747 : Nat.Prime 463747 := by norm_num

private theorem prime_oneHundredFifteenDI_478651 : Nat.Prime 478651 := by norm_num

private theorem prime_oneHundredFifteenDI_498833 : Nat.Prime 498833 := by norm_num

private theorem prime_oneHundredFifteenDI_507589 : Nat.Prime 507589 := by norm_num

private theorem prime_oneHundredFifteenDI_571601 : Nat.Prime 571601 := by norm_num

private theorem prime_oneHundredFifteenDI_578401 : Nat.Prime 578401 := by norm_num

private theorem prime_oneHundredFifteenDI_581261 : Nat.Prime 581261 := by norm_num

private theorem prime_oneHundredFifteenDI_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredFifteenDI_635821 : Nat.Prime 635821 := by norm_num

private theorem prime_oneHundredFifteenDI_637271 : Nat.Prime 637271 := by norm_num

private theorem prime_oneHundredFifteenDI_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredFifteenDI_707827 : Nat.Prime 707827 := by norm_num

private theorem prime_oneHundredFifteenDI_709831 : Nat.Prime 709831 := by norm_num

private theorem prime_oneHundredFifteenDI_720617 : Nat.Prime 720617 := by norm_num

private theorem prime_oneHundredFifteenDI_736363 : Nat.Prime 736363 := by norm_num

private theorem prime_oneHundredFifteenDI_757583 : Nat.Prime 757583 := by norm_num

private theorem prime_oneHundredFifteenDI_769309 : Nat.Prime 769309 := by norm_num

private theorem prime_oneHundredFifteenDI_834013 : Nat.Prime 834013 := by norm_num

private theorem prime_oneHundredFifteenDI_922457 : Nat.Prime 922457 := by norm_num

private theorem prime_oneHundredFifteenDI_958829 : Nat.Prime 958829 := by norm_num

private theorem prime_oneHundredFifteenDI_964661 : Nat.Prime 964661 := by norm_num

private theorem prime_oneHundredFifteenDI_990637 : Nat.Prime 990637 := by norm_num

private theorem prime_oneHundredFifteenDI_1018447 : Nat.Prime 1018447 := by norm_num

private theorem prime_oneHundredFifteenDI_1048759 : Nat.Prime 1048759 := by norm_num

private theorem prime_oneHundredFifteenDI_1088447 : Nat.Prime 1088447 := by norm_num

private theorem prime_oneHundredFifteenDI_1174267 : Nat.Prime 1174267 := by norm_num

private theorem prime_oneHundredFifteenDI_1217509 : Nat.Prime 1217509 := by norm_num

private theorem prime_oneHundredFifteenDI_1224677 : Nat.Prime 1224677 := by norm_num

private theorem prime_oneHundredFifteenDI_1283957 : Nat.Prime 1283957 := by norm_num

private theorem prime_oneHundredFifteenDI_1417271 : Nat.Prime 1417271 := by norm_num

private theorem prime_oneHundredFifteenDI_1436537 : Nat.Prime 1436537 := by norm_num

private theorem prime_oneHundredFifteenDI_1450877 : Nat.Prime 1450877 := by norm_num

private theorem prime_oneHundredFifteenDI_1460497 : Nat.Prime 1460497 := by norm_num

private theorem prime_oneHundredFifteenDI_1518589 : Nat.Prime 1518589 := by norm_num

private theorem prime_oneHundredFifteenDI_1562713 : Nat.Prime 1562713 := by norm_num

private theorem prime_oneHundredFifteenDI_1563217 : Nat.Prime 1563217 := by norm_num

private theorem prime_oneHundredFifteenDI_1602697 : Nat.Prime 1602697 := by norm_num

private theorem prime_oneHundredFifteenDI_1696811 : Nat.Prime 1696811 := by norm_num

private theorem prime_oneHundredFifteenDI_1723669 : Nat.Prime 1723669 := by norm_num

private theorem prime_oneHundredFifteenDI_1822307 : Nat.Prime 1822307 := by norm_num

private theorem prime_oneHundredFifteenDI_1831481 : Nat.Prime 1831481 := by norm_num

private theorem prime_oneHundredFifteenDI_1938301 : Nat.Prime 1938301 := by norm_num

private theorem prime_oneHundredFifteenDI_1948313 : Nat.Prime 1948313 := by norm_num

private theorem prime_oneHundredFifteenDI_1963081 : Nat.Prime 1963081 := by norm_num

private theorem prime_oneHundredFifteenDI_2328617 : Nat.Prime 2328617 := by norm_num

private theorem prime_oneHundredFifteenDI_2344333 : Nat.Prime 2344333 := by norm_num

private theorem prime_oneHundredFifteenDI_2527253 : Nat.Prime 2527253 := by norm_num

private theorem prime_oneHundredFifteenDI_2540011 : Nat.Prime 2540011 := by norm_num

private theorem prime_oneHundredFifteenDI_2651837 : Nat.Prime 2651837 := by norm_num

private theorem prime_oneHundredFifteenDI_2666887 : Nat.Prime 2666887 := by norm_num

private theorem prime_oneHundredFifteenDI_2690351 : Nat.Prime 2690351 := by norm_num

private theorem prime_oneHundredFifteenDI_2723701 : Nat.Prime 2723701 := by norm_num

private theorem prime_oneHundredFifteenDI_2792473 : Nat.Prime 2792473 := by norm_num

private theorem prime_oneHundredFifteenDI_2848009 : Nat.Prime 2848009 := by norm_num

private theorem prime_oneHundredFifteenDI_2865383 : Nat.Prime 2865383 := by norm_num

private theorem prime_oneHundredFifteenDI_3197167 : Nat.Prime 3197167 := by norm_num

private theorem prime_oneHundredFifteenDI_3201437 : Nat.Prime 3201437 := by norm_num

private theorem prime_oneHundredFifteenDI_3314141 : Nat.Prime 3314141 := by norm_num

private theorem prime_oneHundredFifteenDI_3410909 : Nat.Prime 3410909 := by norm_num

private theorem prime_oneHundredFifteenDI_3444667 : Nat.Prime 3444667 := by norm_num

private theorem prime_oneHundredFifteenDI_3457261 : Nat.Prime 3457261 := by norm_num

private theorem prime_oneHundredFifteenDI_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredFifteenDI_3628967 : Nat.Prime 3628967 := by norm_num

private theorem prime_oneHundredFifteenDI_3818587 : Nat.Prime 3818587 := by norm_num

private theorem prime_oneHundredFifteenDI_4201583 : Nat.Prime 4201583 := by norm_num

private theorem prime_oneHundredFifteenDI_4209869 : Nat.Prime 4209869 := by norm_num

private theorem prime_oneHundredFifteenDI_4317569 : Nat.Prime 4317569 := by norm_num

private theorem prime_oneHundredFifteenDI_4320223 : Nat.Prime 4320223 := by norm_num

private theorem prime_oneHundredFifteenDI_4370089 : Nat.Prime 4370089 := by norm_num

private theorem prime_oneHundredFifteenDI_4548559 : Nat.Prime 4548559 := by norm_num

private theorem prime_oneHundredFifteenDI_4586191 : Nat.Prime 4586191 := by norm_num

private theorem prime_oneHundredFifteenDI_5004149 : Nat.Prime 5004149 := by norm_num

private theorem prime_oneHundredFifteenDI_5879023 : Nat.Prime 5879023 := by norm_num

private theorem prime_oneHundredFifteenDI_6627851 : Nat.Prime 6627851 := by norm_num

private theorem prime_oneHundredFifteenDI_6728947 : Nat.Prime 6728947 := by norm_num

private theorem prime_oneHundredFifteenDI_6980443 : Nat.Prime 6980443 := by norm_num

private theorem prime_oneHundredFifteenDI_7346627 : Nat.Prime 7346627 := by norm_num

private theorem prime_oneHundredFifteenDI_7775903 : Nat.Prime 7775903 := by norm_num

private theorem prime_oneHundredFifteenDI_8264819 : Nat.Prime 8264819 := by norm_num

private theorem prime_oneHundredFifteenDI_8725481 : Nat.Prime 8725481 := by norm_num

private theorem prime_oneHundredFifteenDI_8870467 : Nat.Prime 8870467 := by norm_num

private theorem prime_oneHundredFifteenDI_9363721 : Nat.Prime 9363721 := by norm_num

private theorem prime_oneHundredFifteenDI_9642827 : Nat.Prime 9642827 := by norm_num

private theorem prime_oneHundredFifteenDI_9740761 : Nat.Prime 9740761 := by norm_num

private theorem prime_oneHundredFifteenDI_10081399 : Nat.Prime 10081399 := by norm_num

private theorem prime_oneHundredFifteenDI_10537463 : Nat.Prime 10537463 := by norm_num

private theorem prime_oneHundredFifteenDI_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFifteenDI_11085881 : Nat.Prime 11085881 := by norm_num

private theorem prime_oneHundredFifteenDI_11671201 : Nat.Prime 11671201 := by norm_num

private theorem prime_oneHundredFifteenDI_11720081 : Nat.Prime 11720081 := by norm_num

private theorem prime_oneHundredFifteenDI_12378007 : Nat.Prime 12378007 := by norm_num

private theorem prime_oneHundredFifteenDI_12453257 : Nat.Prime 12453257 := by norm_num

private theorem prime_oneHundredFifteenDI_13416959 : Nat.Prime 13416959 := by norm_num

private theorem prime_oneHundredFifteenDI_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredFifteenDI_14267987 : Nat.Prime 14267987 := by norm_num

private theorem prime_oneHundredFifteenDI_14330021 : Nat.Prime 14330021 := by norm_num

private theorem prime_oneHundredFifteenDI_14645633 : Nat.Prime 14645633 := by norm_num

private theorem prime_oneHundredFifteenDI_15501091 : Nat.Prime 15501091 := by norm_num

private theorem prime_oneHundredFifteenDI_16899167 : Nat.Prime 16899167 := by norm_num

private theorem prime_oneHundredFifteenDI_17110663 : Nat.Prime 17110663 := by norm_num

private theorem prime_oneHundredFifteenDI_17923307 : Nat.Prime 17923307 := by norm_num

private theorem prime_oneHundredFifteenDI_18890177 : Nat.Prime 18890177 := by norm_num

private theorem prime_oneHundredFifteenDI_19713929 : Nat.Prime 19713929 := by norm_num

private theorem prime_oneHundredFifteenDI_19870973 : Nat.Prime 19870973 := by norm_num

private theorem prime_oneHundredFifteenDI_22031239 : Nat.Prime 22031239 := by norm_num

private theorem prime_oneHundredFifteenDI_22480327 : Nat.Prime 22480327 := by norm_num

private theorem prime_oneHundredFifteenDI_24478231 : Nat.Prime 24478231 := by norm_num

private theorem prime_oneHundredFifteenDI_28090301 : Nat.Prime 28090301 := by norm_num

private theorem prime_oneHundredFifteenDI_29758991 : Nat.Prime 29758991 := by norm_num

private theorem prime_oneHundredFifteenDI_30607303 : Nat.Prime 30607303 := by
  apply lucas_primality 30607303 (5 : ZMod 30607303)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (463747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (463747, 1)] : List FactorBlock).map factorBlockValue).prod) = 30607303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_463747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 30607303) ^ 15303651 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 30607303) ^ 10202434 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 30607303) ^ 2782482 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 30607303) ^ 66 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_33444289 : Nat.Prime 33444289 := by
  apply lucas_primality 33444289 (11 : ZMod 33444289)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (31, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (31, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) = 33444289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_1873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33444289) ^ 16722144 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 11148096 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 1078848 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 17856 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_40174819 : Nat.Prime 40174819 := by
  apply lucas_primality 40174819 (3 : ZMod 40174819)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (131, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (131, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 40174819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_79
      · exact prime_oneHundredFifteenDI_131
      · exact prime_oneHundredFifteenDI_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40174819) ^ 20087409 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40174819) ^ 13391606 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40174819) ^ 508542 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40174819) ^ 306678 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40174819) ^ 62094 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_41198603 : Nat.Prime 41198603 := by
  apply lucas_primality 41198603 (2 : ZMod 41198603)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (6173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (6173, 1)] : List FactorBlock).map factorBlockValue).prod) = 41198603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_47
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_6173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41198603) ^ 20599301 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41198603) ^ 876566 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41198603) ^ 580262 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41198603) ^ 6674 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_41487133 : Nat.Prime 41487133 := by
  apply lucas_primality 41487133 (2 : ZMod 41487133)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3457261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3457261, 1)] : List FactorBlock).map factorBlockValue).prod) = 41487133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_3457261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41487133) ^ 20743566 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41487133) ^ 13829044 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41487133) ^ 12 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_44627389 : Nat.Prime 44627389 := by
  apply lucas_primality 44627389 (2 : ZMod 44627389)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (286073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (286073, 1)] : List FactorBlock).map factorBlockValue).prod) = 44627389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_286073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44627389) ^ 22313694 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44627389) ^ 14875796 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44627389) ^ 3432876 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44627389) ^ 156 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_48739879 : Nat.Prime 48739879 := by
  apply lucas_primality 48739879 (3 : ZMod 48739879)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (37, 1), (6653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (37, 1), (6653, 1)] : List FactorBlock).map factorBlockValue).prod) = 48739879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_6653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48739879) ^ 24369939 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48739879) ^ 16246626 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48739879) ^ 4430898 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48739879) ^ 1317294 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48739879) ^ 7326 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_53222803 : Nat.Prime 53222803 := by
  apply lucas_primality 53222803 (3 : ZMod 53222803)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8870467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8870467, 1)] : List FactorBlock).map factorBlockValue).prod) = 53222803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_8870467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53222803) ^ 26611401 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 53222803) ^ 17740934 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 53222803) ^ 6 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_58233839 : Nat.Prime 58233839 := by
  apply lucas_primality 58233839 (11 : ZMod 58233839)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (97381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (97381, 1)] : List FactorBlock).map factorBlockValue).prod) = 58233839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_97381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 58233839) ^ 29116919 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 4479526 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 2531906 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 598 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_58440433 : Nat.Prime 58440433 := by
  apply lucas_primality 58440433 (5 : ZMod 58440433)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1217509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1217509, 1)] : List FactorBlock).map factorBlockValue).prod) = 58440433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_1217509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 58440433) ^ 29220216 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 58440433) ^ 19480144 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 58440433) ^ 48 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_58444567 : Nat.Prime 58444567 := by
  apply lucas_primality 58444567 (3 : ZMod 58444567)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9740761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9740761, 1)] : List FactorBlock).map factorBlockValue).prod) = 58444567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_9740761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 58444567) ^ 29222283 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 58444567) ^ 19481522 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 58444567) ^ 6 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_63022361 : Nat.Prime 63022361 := by
  apply lucas_primality 63022361 (6 : ZMod 63022361)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (73, 1), (113, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (73, 1), (113, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 63022361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_73
      · exact prime_oneHundredFifteenDI_113
      · exact prime_oneHundredFifteenDI_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 63022361) ^ 31511180 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 63022361) ^ 12604472 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 63022361) ^ 863320 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 63022361) ^ 557720 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 63022361) ^ 329960 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_64180657 : Nat.Prime 64180657 := by
  apply lucas_primality 64180657 (5 : ZMod 64180657)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (445699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (445699, 1)] : List FactorBlock).map factorBlockValue).prod) = 64180657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_445699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 64180657) ^ 32090328 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 64180657) ^ 21393552 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 64180657) ^ 144 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_68947763 : Nat.Prime 68947763 := by
  apply lucas_primality 68947763 (2 : ZMod 68947763)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2651837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2651837, 1)] : List FactorBlock).map factorBlockValue).prod) = 68947763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_2651837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68947763) ^ 34473881 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 68947763) ^ 5303674 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 68947763) ^ 26 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_72491017 : Nat.Prime 72491017 := by
  apply lucas_primality 72491017 (15 : ZMod 72491017)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (283, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (283, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) = 72491017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_283
      · exact prime_oneHundredFifteenDI_821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 72491017) ^ 36245508 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (15 : ZMod 72491017) ^ 24163672 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (15 : ZMod 72491017) ^ 5576232 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (15 : ZMod 72491017) ^ 256152 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (15 : ZMod 72491017) ^ 88296 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_79224553 : Nat.Prime 79224553 := by
  apply lucas_primality 79224553 (15 : ZMod 79224553)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (67, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (67, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) = 79224553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_67
      · exact prime_oneHundredFifteenDI_1493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 79224553) ^ 39612276 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (15 : ZMod 79224553) ^ 26408184 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (15 : ZMod 79224553) ^ 7202232 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (15 : ZMod 79224553) ^ 1182456 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (15 : ZMod 79224553) ^ 53064 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_88758767 : Nat.Prime 88758767 := by
  apply lucas_primality 88758767 (10 : ZMod 88758767)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (31, 1), (75347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (31, 1), (75347, 1)] : List FactorBlock).map factorBlockValue).prod) = 88758767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_75347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 88758767) ^ 44379383 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 88758767) ^ 4671514 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 88758767) ^ 2863186 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 88758767) ^ 1178 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_88812211 : Nat.Prime 88812211 := by
  apply lucas_primality 88812211 (3 : ZMod 88812211)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 88812211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_29
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88812211) ^ 44406105 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 29604070 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 17762442 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 3062490 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2864910 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2400330 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 997890 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_102211363 : Nat.Prime 102211363 := by
  apply lucas_primality 102211363 (3 : ZMod 102211363)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 2), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 2), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) = 102211363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_15643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102211363) ^ 51105681 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 34070454 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 9291942 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 6534 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_118345387 : Nat.Prime 118345387 := by
  apply lucas_primality 118345387 (2 : ZMod 118345387)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (197, 1), (1697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (197, 1), (1697, 1)] : List FactorBlock).map factorBlockValue).prod) = 118345387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_59
      · exact prime_oneHundredFifteenDI_197
      · exact prime_oneHundredFifteenDI_1697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 118345387) ^ 59172693 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 118345387) ^ 39448462 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 118345387) ^ 2005854 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 118345387) ^ 600738 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 118345387) ^ 69738 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_118642841 : Nat.Prime 118642841 := by
  apply lucas_primality 118642841 (3 : ZMod 118642841)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (156109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (156109, 1)] : List FactorBlock).map factorBlockValue).prod) = 118642841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_156109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 118642841) ^ 59321420 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 118642841) ^ 23728568 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 118642841) ^ 6244360 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 118642841) ^ 760 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_120976789 : Nat.Prime 120976789 := by
  apply lucas_primality 120976789 (2 : ZMod 120976789)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10081399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10081399, 1)] : List FactorBlock).map factorBlockValue).prod) = 120976789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_10081399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120976789) ^ 60488394 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 120976789) ^ 40325596 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 120976789) ^ 12 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_124908149 : Nat.Prime 124908149 := by
  apply lucas_primality 124908149 (2 : ZMod 124908149)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (997, 1), (31321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (997, 1), (31321, 1)] : List FactorBlock).map factorBlockValue).prod) = 124908149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_997
      · exact prime_oneHundredFifteenDI_31321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 124908149) ^ 62454074 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124908149) ^ 125284 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 124908149) ^ 3988 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_134499857 : Nat.Prime 134499857 := by
  apply lucas_primality 134499857 (3 : ZMod 134499857)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (251, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (251, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 134499857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_107
      · exact prime_oneHundredFifteenDI_251
      · exact prime_oneHundredFifteenDI_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 134499857) ^ 67249928 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 1257008 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 535856 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 429712 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_141947653 : Nat.Prime 141947653 := by
  apply lucas_primality 141947653 (2 : ZMod 141947653)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (153623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (153623, 1)] : List FactorBlock).map factorBlockValue).prod) = 141947653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_153623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141947653) ^ 70973826 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 141947653) ^ 47315884 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 141947653) ^ 20278236 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 141947653) ^ 12904332 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 141947653) ^ 924 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_159178729 : Nat.Prime 159178729 := by
  apply lucas_primality 159178729 (7 : ZMod 159178729)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (83, 1), (1949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (83, 1), (1949, 1)] : List FactorBlock).map factorBlockValue).prod) = 159178729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_41
      · exact prime_oneHundredFifteenDI_83
      · exact prime_oneHundredFifteenDI_1949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 159178729) ^ 79589364 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 159178729) ^ 53059576 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 159178729) ^ 3882408 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 159178729) ^ 1917816 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 159178729) ^ 81672 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_160699277 : Nat.Prime 160699277 := by
  apply lucas_primality 160699277 (2 : ZMod 160699277)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (40174819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (40174819, 1)] : List FactorBlock).map factorBlockValue).prod) = 160699277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_40174819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 160699277) ^ 80349638 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 160699277) ^ 4 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_163723633 : Nat.Prime 163723633 := by
  apply lucas_primality 163723633 (5 : ZMod 163723633)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (3410909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (3410909, 1)] : List FactorBlock).map factorBlockValue).prod) = 163723633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_3410909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 163723633) ^ 81861816 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 163723633) ^ 54574544 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 163723633) ^ 48 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_164620993 : Nat.Prime 164620993 := by
  apply lucas_primality 164620993 (5 : ZMod 164620993)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (37, 1), (23173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (37, 1), (23173, 1)] : List FactorBlock).map factorBlockValue).prod) = 164620993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_23173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 164620993) ^ 82310496 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 164620993) ^ 54873664 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 164620993) ^ 4449216 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 164620993) ^ 7104 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_165296381 : Nat.Prime 165296381 := by
  apply lucas_primality 165296381 (2 : ZMod 165296381)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (8264819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (8264819, 1)] : List FactorBlock).map factorBlockValue).prod) = 165296381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_8264819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 165296381) ^ 82648190 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 165296381) ^ 33059276 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 165296381) ^ 20 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_173355797 : Nat.Prime 173355797 := by
  apply lucas_primality 173355797 (2 : ZMod 173355797)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (311791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (311791, 1)] : List FactorBlock).map factorBlockValue).prod) = 173355797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_139
      · exact prime_oneHundredFifteenDI_311791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 173355797) ^ 86677898 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 173355797) ^ 1247164 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 173355797) ^ 556 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_182272577 : Nat.Prime 182272577 := by
  apply lucas_primality 182272577 (3 : ZMod 182272577)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (2848009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (2848009, 1)] : List FactorBlock).map factorBlockValue).prod) = 182272577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_2848009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 182272577) ^ 91136288 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 182272577) ^ 64 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_183643819 : Nat.Prime 183643819 := by
  apply lucas_primality 183643819 (2 : ZMod 183643819)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30607303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30607303, 1)] : List FactorBlock).map factorBlockValue).prod) = 183643819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_30607303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 183643819) ^ 91821909 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 183643819) ^ 61214606 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 183643819) ^ 6 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_190157663 : Nat.Prime 190157663 := by
  apply lucas_primality 190157663 (5 : ZMod 190157663)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (5004149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (5004149, 1)] : List FactorBlock).map factorBlockValue).prod) = 190157663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_5004149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 190157663) ^ 95078831 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 190157663) ^ 10008298 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 190157663) ^ 38 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_198474611 : Nat.Prime 198474611 := by
  apply lucas_primality 198474611 (2 : ZMod 198474611)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (97, 1), (204613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (97, 1), (204613, 1)] : List FactorBlock).map factorBlockValue).prod) = 198474611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_97
      · exact prime_oneHundredFifteenDI_204613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 198474611) ^ 99237305 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 198474611) ^ 39694922 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 198474611) ^ 2046130 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 198474611) ^ 970 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_203222153 : Nat.Prime 203222153 := by
  apply lucas_primality 203222153 (3 : ZMod 203222153)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (3628967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (3628967, 1)] : List FactorBlock).map factorBlockValue).prod) = 203222153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_3628967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 203222153) ^ 101611076 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 203222153) ^ 29031736 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 203222153) ^ 56 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_230798803 : Nat.Prime 230798803 := by
  apply lucas_primality 230798803 (2 : ZMod 230798803)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (43, 1), (68813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (43, 1), (68813, 1)] : List FactorBlock).map factorBlockValue).prod) = 230798803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_43
      · exact prime_oneHundredFifteenDI_68813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 230798803) ^ 115399401 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 230798803) ^ 76932934 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 230798803) ^ 17753754 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 230798803) ^ 5367414 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 230798803) ^ 3354 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_233761733 : Nat.Prime 233761733 := by
  apply lucas_primality 233761733 (2 : ZMod 233761733)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (58440433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (58440433, 1)] : List FactorBlock).map factorBlockValue).prod) = 233761733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_58440433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 233761733) ^ 116880866 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 233761733) ^ 4 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_233793281 : Nat.Prime 233793281 := by
  apply lucas_primality 233793281 (3 : ZMod 233793281)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (7, 1), (97, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (7, 1), (97, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 233793281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_97
      · exact prime_oneHundredFifteenDI_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 233793281) ^ 116896640 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 233793281) ^ 46758656 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 233793281) ^ 33399040 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 233793281) ^ 2410240 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 233793281) ^ 869120 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_238816003 : Nat.Prime 238816003 := by
  apply lucas_primality 238816003 (2 : ZMod 238816003)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (1283957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (1283957, 1)] : List FactorBlock).map factorBlockValue).prod) = 238816003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_1283957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 238816003) ^ 119408001 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 238816003) ^ 79605334 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 238816003) ^ 7703742 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 238816003) ^ 186 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_248828897 : Nat.Prime 248828897 := by
  apply lucas_primality 248828897 (3 : ZMod 248828897)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7775903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7775903, 1)] : List FactorBlock).map factorBlockValue).prod) = 248828897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7775903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 248828897) ^ 124414448 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 248828897) ^ 32 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_249816299 : Nat.Prime 249816299 := by
  apply lucas_primality 249816299 (2 : ZMod 249816299)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (124908149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (124908149, 1)] : List FactorBlock).map factorBlockValue).prod) = 249816299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_124908149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 249816299) ^ 124908149 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 249816299) ^ 2 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_257576009 : Nat.Prime 257576009 := by
  apply lucas_primality 257576009 (3 : ZMod 257576009)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (1277, 1), (1327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (1277, 1), (1327, 1)] : List FactorBlock).map factorBlockValue).prod) = 257576009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_1277
      · exact prime_oneHundredFifteenDI_1327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 257576009) ^ 128788004 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 257576009) ^ 13556632 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 257576009) ^ 201704 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 257576009) ^ 194104 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_260136749 : Nat.Prime 260136749 := by
  apply lucas_primality 260136749 (2 : ZMod 260136749)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (389, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (389, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod) = 260136749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_389
      · exact prime_oneHundredFifteenDI_5393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 260136749) ^ 130068374 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 260136749) ^ 8391508 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 260136749) ^ 668732 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 260136749) ^ 48236 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_264462479 : Nat.Prime 264462479 := by
  apply lucas_primality 264462479 (7 : ZMod 264462479)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (18890177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (18890177, 1)] : List FactorBlock).map factorBlockValue).prod) = 264462479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_18890177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 264462479) ^ 132231239 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 264462479) ^ 37780354 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 264462479) ^ 14 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_290212613 : Nat.Prime 290212613 := by
  apply lucas_primality 290212613 (2 : ZMod 290212613)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (3818587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (3818587, 1)] : List FactorBlock).map factorBlockValue).prod) = 290212613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_3818587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 290212613) ^ 145106306 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 290212613) ^ 15274348 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 290212613) ^ 76 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_323999041 : Nat.Prime 323999041 := by
  apply lucas_primality 323999041 (23 : ZMod 323999041)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (547, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (547, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 323999041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_547
      · exact prime_oneHundredFifteenDI_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 323999041) ^ 161999520 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 323999041) ^ 107999680 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 323999041) ^ 64799808 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 323999041) ^ 592320 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 323999041) ^ 525120 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_337083613 : Nat.Prime 337083613 := by
  apply lucas_primality 337083613 (2 : ZMod 337083613)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (28090301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (28090301, 1)] : List FactorBlock).map factorBlockValue).prod) = 337083613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_28090301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 337083613) ^ 168541806 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 337083613) ^ 112361204 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 337083613) ^ 12 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_361424183 : Nat.Prime 361424183 := by
  apply lucas_primality 361424183 (5 : ZMod 361424183)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (1518589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (1518589, 1)] : List FactorBlock).map factorBlockValue).prod) = 361424183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_17
      · exact prime_oneHundredFifteenDI_1518589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 361424183) ^ 180712091 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 51632026 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 21260246 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 238 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_12539
      · exact prime_oneHundredFifteenDI_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_367056719 : Nat.Prime 367056719 := by
  apply lucas_primality 367056719 (14 : ZMod 367056719)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2347, 1), (11171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2347, 1), (11171, 1)] : List FactorBlock).map factorBlockValue).prod) = 367056719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_2347
      · exact prime_oneHundredFifteenDI_11171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 367056719) ^ 183528359 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (14 : ZMod 367056719) ^ 52436674 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (14 : ZMod 367056719) ^ 156394 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (14 : ZMod 367056719) ^ 32858 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_371540651 : Nat.Prime 371540651 := by
  apply lucas_primality 371540651 (2 : ZMod 371540651)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (571601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (571601, 1)] : List FactorBlock).map factorBlockValue).prod) = 371540651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_571601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 371540651) ^ 185770325 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 371540651) ^ 74308130 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 371540651) ^ 28580050 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 371540651) ^ 650 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_404455027 : Nat.Prime 404455027 := by
  apply lucas_primality 404455027 (3 : ZMod 404455027)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (607, 1), (111053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (607, 1), (111053, 1)] : List FactorBlock).map factorBlockValue).prod) = 404455027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_607
      · exact prime_oneHundredFifteenDI_111053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 404455027) ^ 202227513 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 404455027) ^ 134818342 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 404455027) ^ 666318 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 404455027) ^ 3642 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_410655913 : Nat.Prime 410655913 := by
  apply lucas_primality 410655913 (5 : ZMod 410655913)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17110663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17110663, 1)] : List FactorBlock).map factorBlockValue).prod) = 410655913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_17110663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 410655913) ^ 205327956 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 410655913) ^ 136885304 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 410655913) ^ 24 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_423811879 : Nat.Prime 423811879 := by
  apply lucas_primality 423811879 (3 : ZMod 423811879)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (47, 1), (30671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (47, 1), (30671, 1)] : List FactorBlock).map factorBlockValue).prod) = 423811879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_47
      · exact prime_oneHundredFifteenDI_30671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 423811879) ^ 211905939 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 423811879) ^ 141270626 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 423811879) ^ 60544554 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 423811879) ^ 9017274 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 423811879) ^ 13818 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_439582921 : Nat.Prime 439582921 := by
  apply lucas_primality 439582921 (11 : ZMod 439582921)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 2), (74759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 2), (74759, 1)] : List FactorBlock).map factorBlockValue).prod) = 439582921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_74759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 439582921) ^ 219791460 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 439582921) ^ 146527640 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 439582921) ^ 87916584 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 439582921) ^ 62797560 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 439582921) ^ 5880 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_460490489 : Nat.Prime 460490489 := by
  apply lucas_primality 460490489 (3 : ZMod 460490489)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2749, 1), (20939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2749, 1), (20939, 1)] : List FactorBlock).map factorBlockValue).prod) = 460490489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_2749
      · exact prime_oneHundredFifteenDI_20939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 460490489) ^ 230245244 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 460490489) ^ 167512 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 460490489) ^ 21992 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_464709131 : Nat.Prime 464709131 := by
  apply lucas_primality 464709131 (6 : ZMod 464709131)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6793, 1), (6841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6793, 1), (6841, 1)] : List FactorBlock).map factorBlockValue).prod) = 464709131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_6793
      · exact prime_oneHundredFifteenDI_6841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 464709131) ^ 232354565 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 464709131) ^ 92941826 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 464709131) ^ 68410 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 464709131) ^ 67930 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_467586563 : Nat.Prime 467586563 := by
  apply lucas_primality 467586563 (2 : ZMod 467586563)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233793281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233793281, 1)] : List FactorBlock).map factorBlockValue).prod) = 467586563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_233793281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 467586563) ^ 233793281 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 467586563) ^ 2 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_532228031 : Nat.Prime 532228031 := by
  apply lucas_primality 532228031 (11 : ZMod 532228031)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53222803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53222803, 1)] : List FactorBlock).map factorBlockValue).prod) = 532228031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_53222803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 532228031) ^ 266114015 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 532228031) ^ 106445606 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 532228031) ^ 10 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_561270557 : Nat.Prime 561270557 := by
  apply lucas_primality 561270557 (2 : ZMod 561270557)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (1822307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (1822307, 1)] : List FactorBlock).map factorBlockValue).prod) = 561270557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_1822307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 561270557) ^ 280635278 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 80181508 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 51024596 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 308 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_597733831 : Nat.Prime 597733831 := by
  apply lucas_primality 597733831 (3 : ZMod 597733831)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (245981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (245981, 1)] : List FactorBlock).map factorBlockValue).prod) = 597733831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_245981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 597733831) ^ 298866915 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 199244610 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 119546766 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 2430 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_623238851 : Nat.Prime 623238851 := by
  apply lucas_primality 623238851 (7 : ZMod 623238851)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (958829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (958829, 1)] : List FactorBlock).map factorBlockValue).prod) = 623238851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_958829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 623238851) ^ 311619425 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 623238851) ^ 124647770 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 623238851) ^ 47941450 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 623238851) ^ 650 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_690902353 : Nat.Prime 690902353 := by
  apply lucas_primality 690902353 (10 : ZMod 690902353)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 2), (127, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 2), (127, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 690902353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_127
      · exact prime_oneHundredFifteenDI_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 690902353) ^ 345451176 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 690902353) ^ 230300784 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 690902353) ^ 98700336 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 690902353) ^ 5440176 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 690902353) ^ 2688336 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_17203
      · exact prime_oneHundredFifteenDI_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_722848367 : Nat.Prime 722848367 := by
  apply lucas_primality 722848367 (5 : ZMod 722848367)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (361424183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (361424183, 1)] : List FactorBlock).map factorBlockValue).prod) = 722848367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_361424183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 722848367) ^ 361424183 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 722848367) ^ 2 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_826014271 : Nat.Prime 826014271 := by
  apply lucas_primality 826014271 (6 : ZMod 826014271)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (389, 1), (1913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (389, 1), (1913, 1)] : List FactorBlock).map factorBlockValue).prod) = 826014271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_389
      · exact prime_oneHundredFifteenDI_1913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 826014271) ^ 413007135 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 826014271) ^ 275338090 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 826014271) ^ 165202854 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 826014271) ^ 22324710 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 826014271) ^ 2123430 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 826014271) ^ 431790 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_865679951 : Nat.Prime 865679951 := by
  apply lucas_primality 865679951 (11 : ZMod 865679951)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (1018447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (1018447, 1)] : List FactorBlock).map factorBlockValue).prod) = 865679951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_17
      · exact prime_oneHundredFifteenDI_1018447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 865679951) ^ 432839975 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 865679951) ^ 173135990 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 865679951) ^ 50922350 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 865679951) ^ 850 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1019024263 : Nat.Prime 1019024263 := by
  apply lucas_primality 1019024263 (3 : ZMod 1019024263)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1231, 1), (45989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1231, 1), (45989, 1)] : List FactorBlock).map factorBlockValue).prod) = 1019024263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_1231
      · exact prime_oneHundredFifteenDI_45989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1019024263) ^ 509512131 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1019024263) ^ 339674754 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1019024263) ^ 827802 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1019024263) ^ 22158 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1291988273 : Nat.Prime 1291988273 := by
  apply lucas_primality 1291988273 (3 : ZMod 1291988273)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (127, 1), (635821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (127, 1), (635821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291988273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_127
      · exact prime_oneHundredFifteenDI_635821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1291988273) ^ 645994136 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1291988273) ^ 10173136 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1291988273) ^ 2032 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1427244191 : Nat.Prime 1427244191 := by
  apply lucas_primality 1427244191 (7 : ZMod 1427244191)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (641, 1), (222659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (641, 1), (222659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1427244191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_641
      · exact prime_oneHundredFifteenDI_222659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1427244191) ^ 713622095 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 285448838 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 2226590 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 6410 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1650268649 : Nat.Prime 1650268649 := by
  apply lucas_primality 1650268649 (3 : ZMod 1650268649)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (4209869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (4209869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1650268649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_4209869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1650268649) ^ 825134324 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650268649) ^ 235752664 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650268649) ^ 392 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1704302833 : Nat.Prime 1704302833 := by
  apply lucas_primality 1704302833 (5 : ZMod 1704302833)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (3527, 1), (10067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (3527, 1), (10067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1704302833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_3527
      · exact prime_oneHundredFifteenDI_10067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1704302833) ^ 852151416 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1704302833) ^ 568100944 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1704302833) ^ 483216 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1704302833) ^ 169296 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1983556573 : Nat.Prime 1983556573 := by
  apply lucas_primality 1983556573 (2 : ZMod 1983556573)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (165296381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (165296381, 1)] : List FactorBlock).map factorBlockValue).prod) = 1983556573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_165296381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1983556573) ^ 991778286 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983556573) ^ 661185524 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1983556573) ^ 12 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2190099601 : Nat.Prime 2190099601 := by
  apply lucas_primality 2190099601 (11 : ZMod 2190099601)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (13, 1), (19, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (13, 1), (19, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) = 2190099601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2190099601) ^ 1095049800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2190099601) ^ 730033200 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2190099601) ^ 438019920 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2190099601) ^ 168469200 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2190099601) ^ 115268400 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2190099601) ^ 2667600 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2489993071 : Nat.Prime 2489993071 := by
  apply lucas_primality 2489993071 (6 : ZMod 2489993071)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (37, 1), (103, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (37, 1), (103, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) = 2489993071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_29
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_103
      · exact prime_oneHundredFifteenDI_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2489993071) ^ 1244996535 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2489993071) ^ 829997690 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2489993071) ^ 497998614 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2489993071) ^ 85861830 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2489993071) ^ 67297110 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2489993071) ^ 24174690 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2489993071) ^ 3315570 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2704350581 : Nat.Prime 2704350581 := by
  apply lucas_primality 2704350581 (2 : ZMod 2704350581)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (5879023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (5879023, 1)] : List FactorBlock).map factorBlockValue).prod) = 2704350581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_5879023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2704350581) ^ 1352175290 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704350581) ^ 540870116 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704350581) ^ 117580460 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704350581) ^ 460 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2719869137 : Nat.Prime 2719869137 := by
  apply lucas_primality 2719869137 (3 : ZMod 2719869137)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (71, 1), (97, 1), (24683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (71, 1), (97, 1), (24683, 1)] : List FactorBlock).map factorBlockValue).prod) = 2719869137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_97
      · exact prime_oneHundredFifteenDI_24683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2719869137) ^ 1359934568 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2719869137) ^ 38308016 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2719869137) ^ 28039888 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2719869137) ^ 110192 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2811421681 : Nat.Prime 2811421681 := by
  apply lucas_primality 2811421681 (11 : ZMod 2811421681)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (61, 1), (192037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (61, 1), (192037, 1)] : List FactorBlock).map factorBlockValue).prod) = 2811421681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_61
      · exact prime_oneHundredFifteenDI_192037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2811421681) ^ 1405710840 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2811421681) ^ 937140560 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2811421681) ^ 562284336 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2811421681) ^ 46088880 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 2811421681) ^ 14640 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2929126601 : Nat.Prime 2929126601 := by
  apply lucas_primality 2929126601 (3 : ZMod 2929126601)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (14645633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (14645633, 1)] : List FactorBlock).map factorBlockValue).prod) = 2929126601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_14645633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2929126601) ^ 1464563300 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2929126601) ^ 585825320 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2929126601) ^ 200 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_3727725829 : Nat.Prime 3727725829 := by
  apply lucas_primality 3727725829 (2 : ZMod 3727725829)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (823, 1), (16411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (823, 1), (16411, 1)] : List FactorBlock).map factorBlockValue).prod) = 3727725829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_823
      · exact prime_oneHundredFifteenDI_16411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3727725829) ^ 1863862914 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3727725829) ^ 1242575276 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3727725829) ^ 162075036 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3727725829) ^ 4529436 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3727725829) ^ 227148 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_4064733229 : Nat.Prime 4064733229 := by
  apply lucas_primality 4064733229 (2 : ZMod 4064733229)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (239, 1), (1417271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (239, 1), (1417271, 1)] : List FactorBlock).map factorBlockValue).prod) = 4064733229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_239
      · exact prime_oneHundredFifteenDI_1417271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4064733229) ^ 2032366614 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4064733229) ^ 1354911076 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4064733229) ^ 17007252 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4064733229) ^ 2868 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5067837601 : Nat.Prime 5067837601 := by
  apply lucas_primality 5067837601 (17 : ZMod 5067837601)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (7, 1), (301657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (7, 1), (301657, 1)] : List FactorBlock).map factorBlockValue).prod) = 5067837601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_301657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5067837601) ^ 2533918800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 5067837601) ^ 1689279200 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 5067837601) ^ 1013567520 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 5067837601) ^ 723976800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 5067837601) ^ 16800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5711277277 : Nat.Prime 5711277277 := by
  apply lucas_primality 5711277277 (2 : ZMod 5711277277)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (3163, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (3163, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) = 5711277277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_3163
      · exact prime_oneHundredFifteenDI_5573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5711277277) ^ 2855638638 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1903759092 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1805652 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1024812 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5928970109 : Nat.Prime 5928970109 := by
  apply lucas_primality 5928970109 (2 : ZMod 5928970109)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (11671201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (11671201, 1)] : List FactorBlock).map factorBlockValue).prod) = 5928970109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_127
      · exact prime_oneHundredFifteenDI_11671201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5928970109) ^ 2964485054 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5928970109) ^ 46684804 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5928970109) ^ 508 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_6367883461 : Nat.Prime 6367883461 := by
  apply lucas_primality 6367883461 (2 : ZMod 6367883461)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (827, 1), (7549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (827, 1), (7549, 1)] : List FactorBlock).map factorBlockValue).prod) = 6367883461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_17
      · exact prime_oneHundredFifteenDI_827
      · exact prime_oneHundredFifteenDI_7549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6367883461) ^ 3183941730 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6367883461) ^ 2122627820 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6367883461) ^ 1273576692 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6367883461) ^ 374581380 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6367883461) ^ 7699980 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6367883461) ^ 843540 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_10733279119 : Nat.Prime 10733279119 := by
  apply lucas_primality 10733279119 (6 : ZMod 10733279119)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17747, 1), (100799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17747, 1), (100799, 1)] : List FactorBlock).map factorBlockValue).prod) = 10733279119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_17747
      · exact prime_oneHundredFifteenDI_100799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 10733279119) ^ 5366639559 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 10733279119) ^ 3577759706 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 10733279119) ^ 604794 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 10733279119) ^ 106482 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_11307557357 : Nat.Prime 11307557357 := by
  apply lucas_primality 11307557357 (2 : ZMod 11307557357)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (227, 1), (12453257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (227, 1), (12453257, 1)] : List FactorBlock).map factorBlockValue).prod) = 11307557357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_227
      · exact prime_oneHundredFifteenDI_12453257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11307557357) ^ 5653778678 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11307557357) ^ 49813028 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11307557357) ^ 908 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_13048659479 : Nat.Prime 13048659479 := by
  apply lucas_primality 13048659479 (7 : ZMod 13048659479)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6221, 1), (1048759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6221, 1), (1048759, 1)] : List FactorBlock).map factorBlockValue).prod) = 13048659479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_6221
      · exact prime_oneHundredFifteenDI_1048759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 13048659479) ^ 6524329739 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 13048659479) ^ 2097518 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 13048659479) ^ 12442 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_15915896617 : Nat.Prime 15915896617 := by
  apply lucas_primality 15915896617 (5 : ZMod 15915896617)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (17923307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (17923307, 1)] : List FactorBlock).map factorBlockValue).prod) = 15915896617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_17923307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15915896617) ^ 7957948308 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15915896617) ^ 5305298872 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15915896617) ^ 430159368 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15915896617) ^ 888 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_16319214823 : Nat.Prime 16319214823 := by
  apply lucas_primality 16319214823 (3 : ZMod 16319214823)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2719869137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2719869137, 1)] : List FactorBlock).map factorBlockValue).prod) = 16319214823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_2719869137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16319214823) ^ 8159607411 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16319214823) ^ 5439738274 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16319214823) ^ 6 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_16904834081 : Nat.Prime 16904834081 := by
  apply lucas_primality 16904834081 (3 : ZMod 16904834081)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (97, 1), (349, 1), (3121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (97, 1), (349, 1), (3121, 1)] : List FactorBlock).map factorBlockValue).prod) = 16904834081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_97
      · exact prime_oneHundredFifteenDI_349
      · exact prime_oneHundredFifteenDI_3121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16904834081) ^ 8452417040 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16904834081) ^ 3380966816 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16904834081) ^ 174276640 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16904834081) ^ 48437920 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16904834081) ^ 5416480 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_18280779827 : Nat.Prime 18280779827 := by
  apply lucas_primality 18280779827 (2 : ZMod 18280779827)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23291, 1), (392443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23291, 1), (392443, 1)] : List FactorBlock).map factorBlockValue).prod) = 18280779827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_23291
      · exact prime_oneHundredFifteenDI_392443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18280779827) ^ 9140389913 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18280779827) ^ 784886 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 18280779827) ^ 46582 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_19943643233 : Nat.Prime 19943643233 := by
  apply lucas_primality 19943643233 (3 : ZMod 19943643233)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (623238851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (623238851, 1)] : List FactorBlock).map factorBlockValue).prod) = 19943643233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_623238851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 19943643233) ^ 9971821616 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 19943643233) ^ 32 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_20037609601 : Nat.Prime 20037609601 := by
  apply lucas_primality 20037609601 (46 : ZMod 20037609601)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 2), (67, 1), (31153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 2), (67, 1), (31153, 1)] : List FactorBlock).map factorBlockValue).prod) = 20037609601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_67
      · exact prime_oneHundredFifteenDI_31153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (46 : ZMod 20037609601) ^ 10018804800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (46 : ZMod 20037609601) ^ 6679203200 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (46 : ZMod 20037609601) ^ 4007521920 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (46 : ZMod 20037609601) ^ 299068800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (46 : ZMod 20037609601) ^ 643200 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_21084414319 : Nat.Prime 21084414319 := by
  apply lucas_primality 21084414319 (3 : ZMod 21084414319)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 2), (23, 1), (307, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 2), (23, 1), (307, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 21084414319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_307
      · exact prime_oneHundredFifteenDI_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21084414319) ^ 10542207159 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 21084414319) ^ 7028138106 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 21084414319) ^ 1916764938 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 21084414319) ^ 916713666 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 21084414319) ^ 68678874 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 21084414319) ^ 46136574 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_23816494903 : Nat.Prime 23816494903 := by
  apply lucas_primality 23816494903 (3 : ZMod 23816494903)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (277, 1), (14330021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (277, 1), (14330021, 1)] : List FactorBlock).map factorBlockValue).prod) = 23816494903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_277
      · exact prime_oneHundredFifteenDI_14330021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23816494903) ^ 11908247451 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23816494903) ^ 7938831634 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23816494903) ^ 85980126 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 23816494903) ^ 1662 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_26752207429 : Nat.Prime 26752207429 := by
  apply lucas_primality 26752207429 (2 : ZMod 26752207429)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) = 26752207429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_4621
      · exact prime_oneHundredFifteenDI_160813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26752207429) ^ 13376103714 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 8917402476 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 5789268 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 166356 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_28051407961 : Nat.Prime 28051407961 := by
  apply lucas_primality 28051407961 (13 : ZMod 28051407961)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (233761733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (233761733, 1)] : List FactorBlock).map factorBlockValue).prod) = 28051407961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_233761733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 28051407961) ^ 14025703980 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 28051407961) ^ 9350469320 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 28051407961) ^ 5610281592 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 28051407961) ^ 120 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_29601798143 : Nat.Prime 29601798143 := by
  apply lucas_primality 29601798143 (7 : ZMod 29601798143)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2791, 1), (757583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2791, 1), (757583, 1)] : List FactorBlock).map factorBlockValue).prod) = 29601798143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_2791
      · exact prime_oneHundredFifteenDI_757583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29601798143) ^ 14800899071 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 29601798143) ^ 4228828306 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 29601798143) ^ 10606162 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 29601798143) ^ 39074 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_45103926401 : Nat.Prime 45103926401 := by
  apply lucas_primality 45103926401 (3 : ZMod 45103926401)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (13, 1), (83, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (13, 1), (83, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) = 45103926401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_83
      · exact prime_oneHundredFifteenDI_13063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45103926401) ^ 22551963200 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 9020785280 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 3469532800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 543420800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 3452800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_48756319993 : Nat.Prime 48756319993 := by
  apply lucas_primality 48756319993 (5 : ZMod 48756319993)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (109, 1), (991, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (109, 1), (991, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) = 48756319993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_109
      · exact prime_oneHundredFifteenDI_991
      · exact prime_oneHundredFifteenDI_6269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 48756319993) ^ 24378159996 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 48756319993) ^ 16252106664 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 48756319993) ^ 447305688 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 48756319993) ^ 49199112 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 48756319993) ^ 7777368 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_55430399069 : Nat.Prime 55430399069 := by
  apply lucas_primality 55430399069 (2 : ZMod 55430399069)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (541, 1), (2328617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (541, 1), (2328617, 1)] : List FactorBlock).map factorBlockValue).prod) = 55430399069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_541
      · exact prime_oneHundredFifteenDI_2328617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55430399069) ^ 27715199534 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 55430399069) ^ 5039127188 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 55430399069) ^ 102459148 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 55430399069) ^ 23804 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_57549366421 : Nat.Prime 57549366421 := by
  apply lucas_primality 57549366421 (2 : ZMod 57549366421)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (1657, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (1657, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod) = 57549366421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_1657
      · exact prime_oneHundredFifteenDI_6361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57549366421) ^ 28774683210 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57549366421) ^ 19183122140 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57549366421) ^ 11509873284 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57549366421) ^ 8221338060 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57549366421) ^ 4426874340 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57549366421) ^ 34731060 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57549366421) ^ 9047220 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_61742918101 : Nat.Prime 61742918101 := by
  apply lucas_primality 61742918101 (6 : ZMod 61742918101)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (23, 1), (983, 1), (9103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (23, 1), (983, 1), (9103, 1)] : List FactorBlock).map factorBlockValue).prod) = 61742918101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_983
      · exact prime_oneHundredFifteenDI_9103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 61742918101) ^ 30871459050 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 61742918101) ^ 20580972700 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 61742918101) ^ 12348583620 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 61742918101) ^ 2684474700 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 61742918101) ^ 62810700 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 61742918101) ^ 6782700 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_65276859293 : Nat.Prime 65276859293 := by
  apply lucas_primality 65276859293 (2 : ZMod 65276859293)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16319214823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16319214823, 1)] : List FactorBlock).map factorBlockValue).prod) = 65276859293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_16319214823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 65276859293) ^ 32638429646 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 65276859293) ^ 4 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_86288292067 : Nat.Prime 86288292067 := by
  apply lucas_primality 86288292067 (2 : ZMod 86288292067)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11743, 1), (1224677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11743, 1), (1224677, 1)] : List FactorBlock).map factorBlockValue).prod) = 86288292067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11743
      · exact prime_oneHundredFifteenDI_1224677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 86288292067) ^ 43144146033 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 86288292067) ^ 28762764022 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 86288292067) ^ 7348062 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 86288292067) ^ 70458 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_86330962481 : Nat.Prime 86330962481 := by
  apply lucas_primality 86330962481 (6 : ZMod 86330962481)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (61, 1), (2527253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (61, 1), (2527253, 1)] : List FactorBlock).map factorBlockValue).prod) = 86330962481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_61
      · exact prime_oneHundredFifteenDI_2527253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 86330962481) ^ 43165481240 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 86330962481) ^ 17266192496 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 86330962481) ^ 12332994640 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 86330962481) ^ 1415261680 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 86330962481) ^ 34160 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_91607156309 : Nat.Prime 91607156309 := by
  apply lucas_primality 91607156309 (2 : ZMod 91607156309)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9769, 1), (2344333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9769, 1), (2344333, 1)] : List FactorBlock).map factorBlockValue).prod) = 91607156309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_9769
      · exact prime_oneHundredFifteenDI_2344333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 91607156309) ^ 45803578154 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 91607156309) ^ 9377332 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 91607156309) ^ 39076 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_92012407939 : Nat.Prime 92012407939 := by
  apply lucas_primality 92012407939 (2 : ZMod 92012407939)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (464709131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (464709131, 1)] : List FactorBlock).map factorBlockValue).prod) = 92012407939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_464709131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 92012407939) ^ 46006203969 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92012407939) ^ 30670802646 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92012407939) ^ 8364764358 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92012407939) ^ 198 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_102802990987 : Nat.Prime 102802990987 := by
  apply lucas_primality 102802990987 (3 : ZMod 102802990987)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5711277277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5711277277, 1)] : List FactorBlock).map factorBlockValue).prod) = 102802990987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5711277277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102802990987) ^ 51401495493 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 102802990987) ^ 34267663662 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 102802990987) ^ 18 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_103855260647 : Nat.Prime 103855260647 := by
  apply lucas_primality 103855260647 (5 : ZMod 103855260647)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2357, 1), (22031239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2357, 1), (22031239, 1)] : List FactorBlock).map factorBlockValue).prod) = 103855260647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_2357
      · exact prime_oneHundredFifteenDI_22031239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 103855260647) ^ 51927630323 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 103855260647) ^ 44062478 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 103855260647) ^ 4714 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_115404021211 : Nat.Prime 115404021211 := by
  apply lucas_primality 115404021211 (2 : ZMod 115404021211)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (347, 1), (11085881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (347, 1), (11085881, 1)] : List FactorBlock).map factorBlockValue).prod) = 115404021211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_347
      · exact prime_oneHundredFifteenDI_11085881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 115404021211) ^ 57702010605 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 115404021211) ^ 38468007070 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 115404021211) ^ 23080804242 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 115404021211) ^ 332576430 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 115404021211) ^ 10410 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_135383276201 : Nat.Prime 135383276201 := by
  apply lucas_primality 135383276201 (3 : ZMod 135383276201)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (23, 1), (59, 1), (498833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (23, 1), (59, 1), (498833, 1)] : List FactorBlock).map factorBlockValue).prod) = 135383276201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_59
      · exact prime_oneHundredFifteenDI_498833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 135383276201) ^ 67691638100 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135383276201) ^ 27076655240 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135383276201) ^ 5886229400 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135383276201) ^ 2294631800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135383276201) ^ 271400 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_853
      · exact prime_oneHundredFifteenDI_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_146246238617 : Nat.Prime 146246238617 := by
  apply lucas_primality 146246238617 (3 : ZMod 146246238617)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (18280779827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (18280779827, 1)] : List FactorBlock).map factorBlockValue).prod) = 146246238617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_18280779827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 146246238617) ^ 73123119308 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 146246238617) ^ 8 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_163899569089 : Nat.Prime 163899569089 := by
  apply lucas_primality 163899569089 (37 : ZMod 163899569089)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (89, 1), (3197167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (89, 1), (3197167, 1)] : List FactorBlock).map factorBlockValue).prod) = 163899569089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_89
      · exact prime_oneHundredFifteenDI_3197167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (37 : ZMod 163899569089) ^ 81949784544 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (37 : ZMod 163899569089) ^ 54633189696 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (37 : ZMod 163899569089) ^ 1841568192 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (37 : ZMod 163899569089) ^ 51264 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_195145778351 : Nat.Prime 195145778351 := by
  apply lucas_primality 195145778351 (17 : ZMod 195145778351)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (4231, 1), (922457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (4231, 1), (922457, 1)] : List FactorBlock).map factorBlockValue).prod) = 195145778351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_4231
      · exact prime_oneHundredFifteenDI_922457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 195145778351) ^ 97572889175 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 195145778351) ^ 39029155670 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 195145778351) ^ 46122850 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 195145778351) ^ 211550 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_198631731323 : Nat.Prime 198631731323 := by
  apply lucas_primality 198631731323 (2 : ZMod 198631731323)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (63533, 1), (1563217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (63533, 1), (1563217, 1)] : List FactorBlock).map factorBlockValue).prod) = 198631731323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_63533
      · exact prime_oneHundredFifteenDI_1563217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 198631731323) ^ 99315865661 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 198631731323) ^ 3126434 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 198631731323) ^ 127066 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_249928128199 : Nat.Prime 249928128199 := by
  apply lucas_primality 249928128199 (6 : ZMod 249928128199)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (1983556573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (1983556573, 1)] : List FactorBlock).map factorBlockValue).prod) = 249928128199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_1983556573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 249928128199) ^ 124964064099 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 249928128199) ^ 83309376066 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 249928128199) ^ 35704018314 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 249928128199) ^ 126 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_270905537843 : Nat.Prime 270905537843 := by
  apply lucas_primality 270905537843 (2 : ZMod 270905537843)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (136733, 1), (990637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (136733, 1), (990637, 1)] : List FactorBlock).map factorBlockValue).prod) = 270905537843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_136733
      · exact prime_oneHundredFifteenDI_990637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 270905537843) ^ 135452768921 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 270905537843) ^ 1981274 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 270905537843) ^ 273466 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_271753228993 : Nat.Prime 271753228993 := by
  apply lucas_primality 271753228993 (17 : ZMod 271753228993)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (103, 1), (1963081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (103, 1), (1963081, 1)] : List FactorBlock).map factorBlockValue).prod) = 271753228993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_103
      · exact prime_oneHundredFifteenDI_1963081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 271753228993) ^ 135876614496 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 271753228993) ^ 90584409664 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 271753228993) ^ 38821889856 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 271753228993) ^ 2638380864 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (17 : ZMod 271753228993) ^ 138432 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_309185255989 : Nat.Prime 309185255989 := by
  apply lucas_primality 309185255989 (6 : ZMod 309185255989)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (7537, 1), (162787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (7537, 1), (162787, 1)] : List FactorBlock).map factorBlockValue).prod) = 309185255989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_7537
      · exact prime_oneHundredFifteenDI_162787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 309185255989) ^ 154592627994 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 103061751996 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 44169322284 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 41022324 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 1899324 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_411211963949 : Nat.Prime 411211963949 := by
  apply lucas_primality 411211963949 (2 : ZMod 411211963949)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (102802990987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (102802990987, 1)] : List FactorBlock).map factorBlockValue).prod) = 411211963949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_102802990987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 411211963949) ^ 205605981974 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 411211963949) ^ 4 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_418318835929 : Nat.Prime 418318835929 := by
  apply lucas_primality 418318835929 (13 : ZMod 418318835929)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (2489993071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (2489993071, 1)] : List FactorBlock).map factorBlockValue).prod) = 418318835929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_2489993071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 418318835929) ^ 209159417964 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 418318835929) ^ 139439611976 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 418318835929) ^ 59759833704 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 418318835929) ^ 168 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_418994616571 : Nat.Prime 418994616571 := by
  apply lucas_primality 418994616571 (2 : ZMod 418994616571)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5237, 1), (2666887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5237, 1), (2666887, 1)] : List FactorBlock).map factorBlockValue).prod) = 418994616571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_5237
      · exact prime_oneHundredFifteenDI_2666887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 418994616571) ^ 209497308285 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 418994616571) ^ 139664872190 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 418994616571) ^ 83798923314 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 418994616571) ^ 80006610 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 418994616571) ^ 157110 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_452656745461 : Nat.Prime 452656745461 := by
  apply lucas_primality 452656745461 (2 : ZMod 452656745461)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (2441, 1), (60601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (2441, 1), (60601, 1)] : List FactorBlock).map factorBlockValue).prod) = 452656745461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_17
      · exact prime_oneHundredFifteenDI_2441
      · exact prime_oneHundredFifteenDI_60601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 452656745461) ^ 226328372730 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452656745461) ^ 150885581820 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452656745461) ^ 90531349092 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452656745461) ^ 26626867380 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452656745461) ^ 185439060 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452656745461) ^ 7469460 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_565985657183 : Nat.Prime 565985657183 := by
  apply lucas_primality 565985657183 (5 : ZMod 565985657183)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1051, 1), (24478231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1051, 1), (24478231, 1)] : List FactorBlock).map factorBlockValue).prod) = 565985657183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_1051
      · exact prime_oneHundredFifteenDI_24478231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 565985657183) ^ 282992828591 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 565985657183) ^ 51453241562 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 565985657183) ^ 538521082 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 565985657183) ^ 23122 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_567203840477 : Nat.Prime 567203840477 := by
  apply lucas_primality 567203840477 (3 : ZMod 567203840477)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (1327, 1), (1174267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (1327, 1), (1174267, 1)] : List FactorBlock).map factorBlockValue).prod) = 567203840477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_1327
      · exact prime_oneHundredFifteenDI_1174267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 567203840477) ^ 283601920238 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 567203840477) ^ 81029120068 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 567203840477) ^ 43631064652 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 567203840477) ^ 427433188 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 567203840477) ^ 483028 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_617429181011 : Nat.Prime 617429181011 := by
  apply lucas_primality 617429181011 (2 : ZMod 617429181011)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61742918101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61742918101, 1)] : List FactorBlock).map factorBlockValue).prod) = 617429181011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_61742918101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 617429181011) ^ 308714590505 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 617429181011) ^ 123485836202 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 617429181011) ^ 10 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_629816716439 : Nat.Prime 629816716439 := by
  apply lucas_primality 629816716439 (11 : ZMod 629816716439)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (71, 1), (48739879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (71, 1), (48739879, 1)] : List FactorBlock).map factorBlockValue).prod) = 629816716439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_48739879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 629816716439) ^ 314908358219 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 629816716439) ^ 89973816634 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 629816716439) ^ 48447439726 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 629816716439) ^ 8870657978 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 629816716439) ^ 12922 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_652500499153 : Nat.Prime 652500499153 := by
  apply lucas_primality 652500499153 (5 : ZMod 652500499153)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (659, 1), (827, 1), (24943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (659, 1), (827, 1), (24943, 1)] : List FactorBlock).map factorBlockValue).prod) = 652500499153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_659
      · exact prime_oneHundredFifteenDI_827
      · exact prime_oneHundredFifteenDI_24943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 652500499153) ^ 326250249576 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 652500499153) ^ 217500166384 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 652500499153) ^ 990137328 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 652500499153) ^ 788996976 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 652500499153) ^ 26159664 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_695528511157 : Nat.Prime 695528511157 := by
  apply lucas_primality 695528511157 (2 : ZMod 695528511157)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (29, 1), (2801, 1), (79283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (29, 1), (2801, 1), (79283, 1)] : List FactorBlock).map factorBlockValue).prod) = 695528511157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_29
      · exact prime_oneHundredFifteenDI_2801
      · exact prime_oneHundredFifteenDI_79283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 695528511157) ^ 347764255578 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 695528511157) ^ 231842837052 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 695528511157) ^ 23983741764 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 695528511157) ^ 248314356 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 695528511157) ^ 8772732 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_967951007879 : Nat.Prime 967951007879 := by
  apply lucas_primality 967951007879 (7 : ZMod 967951007879)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1051, 1), (460490489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1051, 1), (460490489, 1)] : List FactorBlock).map factorBlockValue).prod) = 967951007879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_1051
      · exact prime_oneHundredFifteenDI_460490489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 967951007879) ^ 483975503939 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 967951007879) ^ 920980978 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 967951007879) ^ 2102 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1459366549967 : Nat.Prime 1459366549967 := by
  apply lucas_primality 1459366549967 (5 : ZMod 1459366549967)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (67, 1), (179, 1), (409, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (67, 1), (179, 1), (409, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1459366549967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_67
      · exact prime_oneHundredFifteenDI_179
      · exact prime_oneHundredFifteenDI_409
      · exact prime_oneHundredFifteenDI_11443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1459366549967) ^ 729683274983 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 112258965382 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 21781590298 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 8152885754 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 3568133374 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 127533562 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1763290707253 : Nat.Prime 1763290707253 := by
  apply lucas_primality 1763290707253 (2 : ZMod 1763290707253)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (263, 1), (6367, 1), (87751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (263, 1), (6367, 1), (87751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1763290707253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_263
      · exact prime_oneHundredFifteenDI_6367
      · exact prime_oneHundredFifteenDI_87751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1763290707253) ^ 881645353626 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1763290707253) ^ 587763569084 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1763290707253) ^ 6704527404 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1763290707253) ^ 276942156 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1763290707253) ^ 20094252 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1887718368409 : Nat.Prime 1887718368409 := by
  apply lucas_primality 1887718368409 (7 : ZMod 1887718368409)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (94309, 1), (834013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (94309, 1), (834013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1887718368409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_94309
      · exact prime_oneHundredFifteenDI_834013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1887718368409) ^ 943859184204 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1887718368409) ^ 629239456136 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1887718368409) ^ 20016312 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1887718368409) ^ 2263416 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1976076253357 : Nat.Prime 1976076253357 := by
  apply lucas_primality 1976076253357 (2 : ZMod 1976076253357)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (401, 1), (410655913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (401, 1), (410655913, 1)] : List FactorBlock).map factorBlockValue).prod) = 1976076253357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_401
      · exact prime_oneHundredFifteenDI_410655913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1976076253357) ^ 988038126678 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1976076253357) ^ 658692084452 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1976076253357) ^ 4927870956 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1976076253357) ^ 4812 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2475731011073 : Nat.Prime 2475731011073 := by
  apply lucas_primality 2475731011073 (3 : ZMod 2475731011073)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (11, 1), (439582921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (11, 1), (439582921, 1)] : List FactorBlock).map factorBlockValue).prod) = 2475731011073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_439582921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2475731011073) ^ 1237865505536 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2475731011073) ^ 225066455552 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2475731011073) ^ 5632 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2542830126457 : Nat.Prime 2542830126457 := by
  apply lucas_primality 2542830126457 (5 : ZMod 2542830126457)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (47, 1), (313, 1), (248351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (47, 1), (313, 1), (248351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2542830126457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_29
      · exact prime_oneHundredFifteenDI_47
      · exact prime_oneHundredFifteenDI_313
      · exact prime_oneHundredFifteenDI_248351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2542830126457) ^ 1271415063228 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2542830126457) ^ 847610042152 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2542830126457) ^ 87683797464 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2542830126457) ^ 54102768648 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2542830126457) ^ 8124057912 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2542830126457) ^ 10238856 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2577668428667 : Nat.Prime 2577668428667 := by
  apply lucas_primality 2577668428667 (2 : ZMod 2577668428667)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4441, 1), (290212613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4441, 1), (290212613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2577668428667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_4441
      · exact prime_oneHundredFifteenDI_290212613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2577668428667) ^ 1288834214333 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577668428667) ^ 580425226 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577668428667) ^ 8882 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2688025964303 : Nat.Prime 2688025964303 := by
  apply lucas_primality 2688025964303 (5 : ZMod 2688025964303)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (157, 1), (449, 1), (2723701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (157, 1), (449, 1), (2723701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2688025964303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_157
      · exact prime_oneHundredFifteenDI_449
      · exact prime_oneHundredFifteenDI_2723701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2688025964303) ^ 1344012982151 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2688025964303) ^ 384003709186 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2688025964303) ^ 17121184486 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2688025964303) ^ 5986694798 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2688025964303) ^ 986902 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_4148415406349 : Nat.Prime 4148415406349 := by
  apply lucas_primality 4148415406349 (2 : ZMod 4148415406349)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (16573, 1), (157627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (16573, 1), (157627, 1)] : List FactorBlock).map factorBlockValue).prod) = 4148415406349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_397
      · exact prime_oneHundredFifteenDI_16573
      · exact prime_oneHundredFifteenDI_157627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4148415406349) ^ 2074207703174 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 10449409084 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 250311676 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 26317924 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5872927549553 : Nat.Prime 5872927549553 := by
  apply lucas_primality 5872927549553 (3 : ZMod 5872927549553)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (29, 1), (31, 1), (6733, 1), (8663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (29, 1), (31, 1), (6733, 1), (8663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5872927549553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_29
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_6733
      · exact prime_oneHundredFifteenDI_8663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5872927549553) ^ 2936463774776 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5872927549553) ^ 838989649936 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5872927549553) ^ 202514743088 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5872927549553) ^ 189449275792 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5872927549553) ^ 872260144 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5872927549553) ^ 677932304 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5876800637101 : Nat.Prime 5876800637101 := by
  apply lucas_primality 5876800637101 (2 : ZMod 5876800637101)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (31, 1), (2333, 1), (270859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (31, 1), (2333, 1), (270859, 1)] : List FactorBlock).map factorBlockValue).prod) = 5876800637101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_2333
      · exact prime_oneHundredFifteenDI_270859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5876800637101) ^ 2938400318550 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5876800637101) ^ 1958933545700 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5876800637101) ^ 1175360127420 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5876800637101) ^ 189574214100 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5876800637101) ^ 2518988700 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5876800637101) ^ 21696900 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_7019819453617 : Nat.Prime 7019819453617 := by
  apply lucas_primality 7019819453617 (7 : ZMod 7019819453617)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (146246238617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (146246238617, 1)] : List FactorBlock).map factorBlockValue).prod) = 7019819453617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_146246238617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 7019819453617) ^ 3509909726808 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 7019819453617) ^ 2339939817872 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 7019819453617) ^ 48 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_7578033636209 : Nat.Prime 7578033636209 := by
  apply lucas_primality 7578033636209 (3 : ZMod 7578033636209)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (41, 1), (1650268649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (41, 1), (1650268649, 1)] : List FactorBlock).map factorBlockValue).prod) = 7578033636209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_41
      · exact prime_oneHundredFifteenDI_1650268649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7578033636209) ^ 3789016818104 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 7578033636209) ^ 1082576233744 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 7578033636209) ^ 184830088688 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 7578033636209) ^ 4592 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_8455531342393 : Nat.Prime 8455531342393 := by
  apply lucas_primality 8455531342393 (5 : ZMod 8455531342393)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (13048659479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (13048659479, 1)] : List FactorBlock).map factorBlockValue).prod) = 8455531342393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_13048659479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8455531342393) ^ 4227765671196 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8455531342393) ^ 2818510447464 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 8455531342393) ^ 648 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_10382993943589 : Nat.Prime 10382993943589 := by
  apply lucas_primality 10382993943589 (13 : ZMod 10382993943589)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (19, 1), (722848367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (19, 1), (722848367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10382993943589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_722848367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10382993943589) ^ 5191496971794 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 3460997981196 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 1483284849084 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 546473365452 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 14364 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_10931500474933 : Nat.Prime 10931500474933 := by
  apply lucas_primality 10931500474933 (2 : ZMod 10931500474933)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (311, 1), (2929126601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (311, 1), (2929126601, 1)] : List FactorBlock).map factorBlockValue).prod) = 10931500474933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_311
      · exact prime_oneHundredFifteenDI_2929126601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10931500474933) ^ 5465750237466 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10931500474933) ^ 3643833491644 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10931500474933) ^ 35149519212 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10931500474933) ^ 3732 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_11727020864261 : Nat.Prime 11727020864261 := by
  apply lucas_primality 11727020864261 (2 : ZMod 11727020864261)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (45103926401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (45103926401, 1)] : List FactorBlock).map factorBlockValue).prod) = 11727020864261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_45103926401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11727020864261) ^ 5863510432130 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 2345404172852 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 902078528020 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 260 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_12898892950747 : Nat.Prime 12898892950747 := by
  apply lucas_primality 12898892950747 (3 : ZMod 12898892950747)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (739, 1), (264462479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (739, 1), (264462479, 1)] : List FactorBlock).map factorBlockValue).prod) = 12898892950747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_739
      · exact prime_oneHundredFifteenDI_264462479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12898892950747) ^ 6449446475373 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12898892950747) ^ 4299630983582 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12898892950747) ^ 1172626631886 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12898892950747) ^ 17454523614 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12898892950747) ^ 48774 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_13509554247451 : Nat.Prime 13509554247451 := by
  apply lucas_primality 13509554247451 (2 : ZMod 13509554247451)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (457, 1), (2273, 1), (28901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (457, 1), (2273, 1), (28901, 1)] : List FactorBlock).map factorBlockValue).prod) = 13509554247451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_457
      · exact prime_oneHundredFifteenDI_2273
      · exact prime_oneHundredFifteenDI_28901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13509554247451) ^ 6754777123725 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13509554247451) ^ 4503184749150 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13509554247451) ^ 2701910849490 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13509554247451) ^ 29561387850 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13509554247451) ^ 5943490650 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13509554247451) ^ 467442450 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_16719052275049 : Nat.Prime 16719052275049 := by
  apply lucas_primality 16719052275049 (7 : ZMod 16719052275049)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (457, 1), (41198603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (457, 1), (41198603, 1)] : List FactorBlock).map factorBlockValue).prod) = 16719052275049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_457
      · exact prime_oneHundredFifteenDI_41198603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16719052275049) ^ 8359526137524 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16719052275049) ^ 5573017425016 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16719052275049) ^ 451866277704 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16719052275049) ^ 36584359464 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 16719052275049) ^ 405816 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_19175562518401 : Nat.Prime 19175562518401 := by
  apply lucas_primality 19175562518401 (38 : ZMod 19175562518401)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (479, 1), (463339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (479, 1), (463339, 1)] : List FactorBlock).map factorBlockValue).prod) = 19175562518401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_479
      · exact prime_oneHundredFifteenDI_463339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 19175562518401) ^ 9587781259200 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 6391854172800 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 3835112503680 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 40032489600 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 41385600 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_19918601169697 : Nat.Prime 19918601169697 := by
  apply lucas_primality 19918601169697 (5 : ZMod 19918601169697)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (19, 1), (404455027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (19, 1), (404455027, 1)] : List FactorBlock).map factorBlockValue).prod) = 19918601169697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_404455027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19918601169697) ^ 9959300584848 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19918601169697) ^ 6639533723232 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19918601169697) ^ 1048347429984 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19918601169697) ^ 49248 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_20951102358793 : Nat.Prime 20951102358793 := by
  apply lucas_primality 20951102358793 (7 : ZMod 20951102358793)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (158881, 1), (1831481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (158881, 1), (1831481, 1)] : List FactorBlock).map factorBlockValue).prod) = 20951102358793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_158881
      · exact prime_oneHundredFifteenDI_1831481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 20951102358793) ^ 10475551179396 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 20951102358793) ^ 6983700786264 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 20951102358793) ^ 131866632 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 20951102358793) ^ 11439432 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_25196867687099 : Nat.Prime 25196867687099 := by
  apply lucas_primality 25196867687099 (2 : ZMod 25196867687099)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (65276859293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (65276859293, 1)] : List FactorBlock).map factorBlockValue).prod) = 25196867687099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_193
      · exact prime_oneHundredFifteenDI_65276859293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25196867687099) ^ 12598433843549 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25196867687099) ^ 130553718586 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25196867687099) ^ 386 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_30118956186889 : Nat.Prime 30118956186889 := by
  apply lucas_primality 30118956186889 (7 : ZMod 30118956186889)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (418318835929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (418318835929, 1)] : List FactorBlock).map factorBlockValue).prod) = 30118956186889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_418318835929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 30118956186889) ^ 15059478093444 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 30118956186889) ^ 10039652062296 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 30118956186889) ^ 72 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_30895301819009 : Nat.Prime 30895301819009 := by
  apply lucas_primality 30895301819009 (3 : ZMod 30895301819009)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (11, 1), (151, 1), (379, 1), (383419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (11, 1), (151, 1), (379, 1), (383419, 1)] : List FactorBlock).map factorBlockValue).prod) = 30895301819009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_151
      · exact prime_oneHundredFifteenDI_379
      · exact prime_oneHundredFifteenDI_383419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30895301819009) ^ 15447650909504 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30895301819009) ^ 2808663801728 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30895301819009) ^ 204604647808 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30895301819009) ^ 81517946752 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30895301819009) ^ 80578432 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_33763383185377 : Nat.Prime 33763383185377 := by
  apply lucas_primality 33763383185377 (11 : ZMod 33763383185377)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (47, 1), (137, 1), (4201583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (47, 1), (137, 1), (4201583, 1)] : List FactorBlock).map factorBlockValue).prod) = 33763383185377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_47
      · exact prime_oneHundredFifteenDI_137
      · exact prime_oneHundredFifteenDI_4201583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33763383185377) ^ 16881691592688 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 11254461061792 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 2597183321952 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 718369855008 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 246448052448 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 8035872 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_58424394937189 : Nat.Prime 58424394937189 := by
  apply lucas_primality 58424394937189 (6 : ZMod 58424394937189)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (695528511157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (695528511157, 1)] : List FactorBlock).map factorBlockValue).prod) = 58424394937189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_695528511157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 58424394937189) ^ 29212197468594 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 58424394937189) ^ 19474798312396 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 58424394937189) ^ 8346342133884 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 58424394937189) ^ 84 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_78625427044883 : Nat.Prime 78625427044883 := by
  apply lucas_primality 78625427044883 (2 : ZMod 78625427044883)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (419, 1), (701, 1), (4317569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (419, 1), (701, 1), (4317569, 1)] : List FactorBlock).map factorBlockValue).prod) = 78625427044883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_419
      · exact prime_oneHundredFifteenDI_701
      · exact prime_oneHundredFifteenDI_4317569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78625427044883) ^ 39312713522441 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78625427044883) ^ 2536304098222 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78625427044883) ^ 187650183878 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78625427044883) ^ 112161807482 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78625427044883) ^ 18210578 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_89250683631929 : Nat.Prime 89250683631929 := by
  apply lucas_primality 89250683631929 (3 : ZMod 89250683631929)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (23, 1), (131, 1), (1747, 1), (23291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (23, 1), (131, 1), (1747, 1), (23291, 1)] : List FactorBlock).map factorBlockValue).prod) = 89250683631929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_131
      · exact prime_oneHundredFifteenDI_1747
      · exact prime_oneHundredFifteenDI_23291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 89250683631929) ^ 44625341815964 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 89250683631929) ^ 12750097661704 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 89250683631929) ^ 6865437202456 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 89250683631929) ^ 3880464505736 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 89250683631929) ^ 681302928488 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 89250683631929) ^ 51087970024 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 89250683631929) ^ 3831981608 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_173
      · exact prime_oneHundredFifteenDI_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_110520540000281 : Nat.Prime 110520540000281 := by
  apply lucas_primality 110520540000281 (3 : ZMod 110520540000281)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (18731, 1), (1460497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (18731, 1), (1460497, 1)] : List FactorBlock).map factorBlockValue).prod) = 110520540000281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_101
      · exact prime_oneHundredFifteenDI_18731
      · exact prime_oneHundredFifteenDI_1460497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 110520540000281) ^ 55260270000140 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 110520540000281) ^ 22104108000056 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 110520540000281) ^ 1094262772280 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 110520540000281) ^ 5900407880 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 110520540000281) ^ 75673240 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_110975628033097 : Nat.Prime 110975628033097 := by
  apply lucas_primality 110975628033097 (5 : ZMod 110975628033097)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (227, 1), (281, 1), (72491017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (227, 1), (281, 1), (72491017, 1)] : List FactorBlock).map factorBlockValue).prod) = 110975628033097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_227
      · exact prime_oneHundredFifteenDI_281
      · exact prime_oneHundredFifteenDI_72491017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 110975628033097) ^ 55487814016548 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 110975628033097) ^ 36991876011032 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 110975628033097) ^ 488879418648 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 110975628033097) ^ 394931060616 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 110975628033097) ^ 1530888 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_147486339107659 : Nat.Prime 147486339107659 := by
  apply lucas_primality 147486339107659 (2 : ZMod 147486339107659)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (115404021211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (115404021211, 1)] : List FactorBlock).map factorBlockValue).prod) = 147486339107659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_115404021211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 147486339107659) ^ 73743169553829 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147486339107659) ^ 49162113035886 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147486339107659) ^ 2077272381798 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147486339107659) ^ 1278 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_157250854089767 : Nat.Prime 157250854089767 := by
  apply lucas_primality 157250854089767 (5 : ZMod 157250854089767)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (78625427044883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (78625427044883, 1)] : List FactorBlock).map factorBlockValue).prod) = 157250854089767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_78625427044883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 157250854089767) ^ 78625427044883 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 157250854089767) ^ 2 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_185503503650249 : Nat.Prime 185503503650249 := by
  apply lucas_primality 185503503650249 (3 : ZMod 185503503650249)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (157, 1), (709, 1), (29758991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (157, 1), (709, 1), (29758991, 1)] : List FactorBlock).map factorBlockValue).prod) = 185503503650249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_157
      · exact prime_oneHundredFifteenDI_709
      · exact prime_oneHundredFifteenDI_29758991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 185503503650249) ^ 92751751825124 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 185503503650249) ^ 26500500521464 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 185503503650249) ^ 1181550978664 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 185503503650249) ^ 261641048872 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 185503503650249) ^ 6233528 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_211648661139247 : Nat.Prime 211648661139247 := by
  apply lucas_primality 211648661139247 (3 : ZMod 211648661139247)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (136949, 1), (257576009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (136949, 1), (257576009, 1)] : List FactorBlock).map factorBlockValue).prod) = 211648661139247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_136949
      · exact prime_oneHundredFifteenDI_257576009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 211648661139247) ^ 105824330569623 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 211648661139247) ^ 70549553713082 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 211648661139247) ^ 1545456054 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 211648661139247) ^ 821694 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_231282552022667 : Nat.Prime 231282552022667 := by
  apply lucas_primality 231282552022667 (2 : ZMod 231282552022667)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (41603, 1), (41487133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (41603, 1), (41487133, 1)] : List FactorBlock).map factorBlockValue).prod) = 231282552022667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_67
      · exact prime_oneHundredFifteenDI_41603
      · exact prime_oneHundredFifteenDI_41487133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 231282552022667) ^ 115641276011333 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 231282552022667) ^ 3451978388398 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 231282552022667) ^ 5559275822 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 231282552022667) ^ 5574802 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_243551771161397 : Nat.Prime 243551771161397 := by
  apply lucas_primality 243551771161397 (2 : ZMod 243551771161397)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (71, 1), (19943643233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (71, 1), (19943643233, 1)] : List FactorBlock).map factorBlockValue).prod) = 243551771161397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_43
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_19943643233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243551771161397) ^ 121775885580698 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 243551771161397) ^ 5663994678172 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 243551771161397) ^ 3430306636076 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 243551771161397) ^ 12212 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_258050492573089 : Nat.Prime 258050492573089 := by
  apply lucas_primality 258050492573089 (7 : ZMod 258050492573089)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2688025964303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2688025964303, 1)] : List FactorBlock).map factorBlockValue).prod) = 258050492573089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_2688025964303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 258050492573089) ^ 129025246286544 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 258050492573089) ^ 86016830857696 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 258050492573089) ^ 96 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_292908789113711 : Nat.Prime 292908789113711 := by
  apply lucas_primality 292908789113711 (19 : ZMod 292908789113711)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (37, 1), (43, 1), (59, 1), (71, 1), (57077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (37, 1), (43, 1), (59, 1), (71, 1), (57077, 1)] : List FactorBlock).map factorBlockValue).prod) = 292908789113711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_43
      · exact prime_oneHundredFifteenDI_59
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_57077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 292908789113711) ^ 146454394556855 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (19 : ZMod 292908789113711) ^ 58581757822742 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (19 : ZMod 292908789113711) ^ 41844112730530 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (19 : ZMod 292908789113711) ^ 26628071737610 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (19 : ZMod 292908789113711) ^ 7916453759830 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (19 : ZMod 292908789113711) ^ 6811832304970 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (19 : ZMod 292908789113711) ^ 4964555747690 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (19 : ZMod 292908789113711) ^ 4125475903010 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (19 : ZMod 292908789113711) ^ 5131818230 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_451066928893627 : Nat.Prime 451066928893627 := by
  apply lucas_primality 451066928893627 (2 : ZMod 451066928893627)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (331, 1), (701, 1), (323999041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (331, 1), (701, 1), (323999041, 1)] : List FactorBlock).map factorBlockValue).prod) = 451066928893627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_331
      · exact prime_oneHundredFifteenDI_701
      · exact prime_oneHundredFifteenDI_323999041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 451066928893627) ^ 225533464446813 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 451066928893627) ^ 150355642964542 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 451066928893627) ^ 1362739966446 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 451066928893627) ^ 643462095426 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 451066928893627) ^ 1392186 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_717656839221107 : Nat.Prime 717656839221107 := by
  apply lucas_primality 717656839221107 (2 : ZMod 717656839221107)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42929, 1), (47947, 1), (174331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42929, 1), (47947, 1), (174331, 1)] : List FactorBlock).map factorBlockValue).prod) = 717656839221107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_42929
      · exact prime_oneHundredFifteenDI_47947
      · exact prime_oneHundredFifteenDI_174331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 717656839221107) ^ 358828419610553 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 717656839221107) ^ 16717296914 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 717656839221107) ^ 14967710998 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 717656839221107) ^ 4116633526 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_805373625772843 : Nat.Prime 805373625772843 := by
  apply lucas_primality 805373625772843 (2 : ZMod 805373625772843)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19175562518401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19175562518401, 1)] : List FactorBlock).map factorBlockValue).prod) = 805373625772843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_19175562518401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 805373625772843) ^ 402686812886421 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 268457875257614 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 115053375110406 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 42 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1010787564908137 : Nat.Prime 1010787564908137 := by
  apply lucas_primality 1010787564908137 (5 : ZMod 1010787564908137)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (720617, 1), (58444567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (720617, 1), (58444567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1010787564908137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_720617
      · exact prime_oneHundredFifteenDI_58444567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1010787564908137) ^ 505393782454068 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1010787564908137) ^ 336929188302712 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1010787564908137) ^ 1402669608 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1010787564908137) ^ 17294808 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1081571503521731 : Nat.Prime 1081571503521731 := by
  apply lucas_primality 1081571503521731 (2 : ZMod 1081571503521731)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (53, 1), (281, 1), (787, 1), (709831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (53, 1), (281, 1), (787, 1), (709831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081571503521731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_53
      · exact prime_oneHundredFifteenDI_281
      · exact prime_oneHundredFifteenDI_787
      · exact prime_oneHundredFifteenDI_709831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081571503521731) ^ 540785751760865 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081571503521731) ^ 216314300704346 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081571503521731) ^ 83197807963210 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081571503521731) ^ 20407009500410 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081571503521731) ^ 3849008909330 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081571503521731) ^ 1374296700790 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081571503521731) ^ 1523702830 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1278975786056377 : Nat.Prime 1278975786056377 := by
  apply lucas_primality 1278975786056377 (5 : ZMod 1278975786056377)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1093, 1), (48756319993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1093, 1), (48756319993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1278975786056377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_1093
      · exact prime_oneHundredFifteenDI_48756319993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1278975786056377) ^ 639487893028188 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1278975786056377) ^ 426325262018792 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1278975786056377) ^ 1170151679832 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1278975786056377) ^ 26232 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1647559854904009 : Nat.Prime 1647559854904009 := by
  apply lucas_primality 1647559854904009 (11 : ZMod 1647559854904009)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (661, 1), (103855260647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (661, 1), (103855260647, 1)] : List FactorBlock).map factorBlockValue).prod) = 1647559854904009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_661
      · exact prime_oneHundredFifteenDI_103855260647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1647559854904009) ^ 823779927452004 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1647559854904009) ^ 549186618301336 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1647559854904009) ^ 2492526255528 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1647559854904009) ^ 15864 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2033780937964471 : Nat.Prime 2033780937964471 := by
  apply lucas_primality 2033780937964471 (6 : ZMod 2033780937964471)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (19, 1), (59, 1), (43793, 1), (153437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (19, 1), (59, 1), (43793, 1), (153437, 1)] : List FactorBlock).map factorBlockValue).prod) = 2033780937964471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_59
      · exact prime_oneHundredFifteenDI_43793
      · exact prime_oneHundredFifteenDI_153437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2033780937964471) ^ 1016890468982235 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2033780937964471) ^ 677926979321490 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2033780937964471) ^ 406756187592894 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2033780937964471) ^ 107041101998130 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2033780937964471) ^ 34470863355330 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2033780937964471) ^ 46440776790 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2033780937964471) ^ 13254827310 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5082163822594319 : Nat.Prime 5082163822594319 := by
  apply lucas_primality 5082163822594319 (13 : ZMod 5082163822594319)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (12898892950747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (12898892950747, 1)] : List FactorBlock).map factorBlockValue).prod) = 5082163822594319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_197
      · exact prime_oneHundredFifteenDI_12898892950747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 5082163822594319) ^ 2541081911297159 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 5082163822594319) ^ 25797785901494 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 5082163822594319) ^ 394 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_6332346050196323 : Nat.Prime 6332346050196323 := by
  apply lucas_primality 6332346050196323 (2 : ZMod 6332346050196323)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (243551771161397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (243551771161397, 1)] : List FactorBlock).map factorBlockValue).prod) = 6332346050196323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_243551771161397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6332346050196323) ^ 3166173025098161 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6332346050196323) ^ 487103542322794 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6332346050196323) ^ 26 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_10848942541098283 : Nat.Prime 10848942541098283 := by
  apply lucas_primality 10848942541098283 (2 : ZMod 10848942541098283)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (581261, 1), (163723633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (581261, 1), (163723633, 1)] : List FactorBlock).map factorBlockValue).prod) = 10848942541098283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_581261
      · exact prime_oneHundredFifteenDI_163723633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10848942541098283) ^ 5424471270549141 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10848942541098283) ^ 3616314180366094 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10848942541098283) ^ 570996975847278 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10848942541098283) ^ 18664494162 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10848942541098283) ^ 66263754 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_11579864862383303 : Nat.Prime 11579864862383303 := by
  apply lucas_primality 11579864862383303 (5 : ZMod 11579864862383303)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12791, 1), (452656745461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12791, 1), (452656745461, 1)] : List FactorBlock).map factorBlockValue).prod) = 11579864862383303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_12791
      · exact prime_oneHundredFifteenDI_452656745461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11579864862383303) ^ 5789932431191651 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 11579864862383303) ^ 905313490922 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 11579864862383303) ^ 25582 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_15452033021388883 : Nat.Prime 15452033021388883 := by
  apply lucas_primality 15452033021388883 (2 : ZMod 15452033021388883)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (83, 1), (195145778351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (83, 1), (195145778351, 1)] : List FactorBlock).map factorBlockValue).prod) = 15452033021388883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_53
      · exact prime_oneHundredFifteenDI_83
      · exact prime_oneHundredFifteenDI_195145778351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15452033021388883) ^ 7726016510694441 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 15452033021388883) ^ 5150677673796294 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 15452033021388883) ^ 291547792856394 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 15452033021388883) ^ 186169072546854 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 15452033021388883) ^ 79182 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_45575005254974837 : Nat.Prime 45575005254974837 := by
  apply lucas_primality 45575005254974837 (2 : ZMod 45575005254974837)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (149, 1), (967951007879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (149, 1), (967951007879, 1)] : List FactorBlock).map factorBlockValue).prod) = 45575005254974837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_79
      · exact prime_oneHundredFifteenDI_149
      · exact prime_oneHundredFifteenDI_967951007879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45575005254974837) ^ 22787502627487418 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45575005254974837) ^ 576898800695884 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45575005254974837) ^ 305872518489764 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45575005254974837) ^ 47084 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_47971420655167609 : Nat.Prime 47971420655167609 := by
  apply lucas_primality 47971420655167609 (7 : ZMod 47971420655167609)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (61, 1), (983, 1), (9677, 1), (3444667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (61, 1), (983, 1), (9677, 1), (3444667, 1)] : List FactorBlock).map factorBlockValue).prod) = 47971420655167609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_61
      · exact prime_oneHundredFifteenDI_983
      · exact prime_oneHundredFifteenDI_9677
      · exact prime_oneHundredFifteenDI_3444667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47971420655167609) ^ 23985710327583804 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47971420655167609) ^ 15990473551722536 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47971420655167609) ^ 786416732051928 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47971420655167609) ^ 48801038306376 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47971420655167609) ^ 4957261615704 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47971420655167609) ^ 13926286824 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_62619462674672521 : Nat.Prime 62619462674672521 := by
  apply lucas_primality 62619462674672521 (23 : ZMod 62619462674672521)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (31, 1), (64709, 1), (260136749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (31, 1), (64709, 1), (260136749, 1)] : List FactorBlock).map factorBlockValue).prod) = 62619462674672521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_64709
      · exact prime_oneHundredFifteenDI_260136749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 62619462674672521) ^ 31309731337336260 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 62619462674672521) ^ 20873154224890840 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 62619462674672521) ^ 12523892534934504 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 62619462674672521) ^ 2019982666924920 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 62619462674672521) ^ 967708706280 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (23 : ZMod 62619462674672521) ^ 240717480 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_83987056188276271 : Nat.Prime 83987056188276271 := by
  apply lucas_primality 83987056188276271 (3 : ZMod 83987056188276271)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (29, 1), (31, 1), (163899569089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (29, 1), (31, 1), (163899569089, 1)] : List FactorBlock).map factorBlockValue).prod) = 83987056188276271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_29
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_163899569089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 83987056188276271) ^ 41993528094138135 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 83987056188276271) ^ 27995685396092090 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 83987056188276271) ^ 16797411237655254 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 83987056188276271) ^ 4420371378330330 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 83987056188276271) ^ 2896105385802630 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 83987056188276271) ^ 2709259877041170 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 83987056188276271) ^ 512430 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_114969019264351177 : Nat.Prime 114969019264351177 := by
  apply lucas_primality 114969019264351177 (10 : ZMod 114969019264351177)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (195469, 1), (597733831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (195469, 1), (597733831, 1)] : List FactorBlock).map factorBlockValue).prod) = 114969019264351177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_41
      · exact prime_oneHundredFifteenDI_195469
      · exact prime_oneHundredFifteenDI_597733831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 114969019264351177) ^ 57484509632175588 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 38323006421450392 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 2804122421081736 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 588170089704 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 192341496 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_135985957393556749 : Nat.Prime 135985957393556749 := by
  apply lucas_primality 135985957393556749 (2 : ZMod 135985957393556749)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (223, 1), (2447, 1), (561270557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (223, 1), (2447, 1), (561270557, 1)] : List FactorBlock).map factorBlockValue).prod) = 135985957393556749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_223
      · exact prime_oneHundredFifteenDI_2447
      · exact prime_oneHundredFifteenDI_561270557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135985957393556749) ^ 67992978696778374 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 45328652464518916 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 3675296145771804 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 609802499522676 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 55572520389684 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 242282364 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_162410613636476713 : Nat.Prime 162410613636476713 := by
  apply lucas_primality 162410613636476713 (5 : ZMod 162410613636476713)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (43, 1), (71, 1), (839, 1), (203222153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (43, 1), (71, 1), (839, 1), (203222153, 1)] : List FactorBlock).map factorBlockValue).prod) = 162410613636476713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_43
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_839
      · exact prime_oneHundredFifteenDI_203222153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 162410613636476713) ^ 81205306818238356 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 162410613636476713) ^ 54136871212158904 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 162410613636476713) ^ 12493124125882824 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 162410613636476713) ^ 3776991014801784 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 162410613636476713) ^ 2287473431499672 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 162410613636476713) ^ 193576416730008 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 162410613636476713) ^ 799177704 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_227657689918035107 : Nat.Prime 227657689918035107 := by
  apply lucas_primality 227657689918035107 (2 : ZMod 227657689918035107)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (1278975786056377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (1278975786056377, 1)] : List FactorBlock).map factorBlockValue).prod) = 227657689918035107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_89
      · exact prime_oneHundredFifteenDI_1278975786056377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 227657689918035107) ^ 113828844959017553 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 227657689918035107) ^ 2557951572112754 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 227657689918035107) ^ 178 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_261318517715367989 : Nat.Prime 261318517715367989 := by
  apply lucas_primality 261318517715367989 (2 : ZMod 261318517715367989)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (997, 1), (1481, 1), (1427244191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (997, 1), (1481, 1), (1427244191, 1)] : List FactorBlock).map factorBlockValue).prod) = 261318517715367989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_997
      · exact prime_oneHundredFifteenDI_1481
      · exact prime_oneHundredFifteenDI_1427244191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 261318517715367989) ^ 130659258857683994 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 8429629603721548 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 262104832212004 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 176447344844948 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 183093068 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_305185311208195361 : Nat.Prime 305185311208195361 := by
  apply lucas_primality 305185311208195361 (3 : ZMod 305185311208195361)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (71, 1), (141277, 1), (190157663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (71, 1), (141277, 1), (190157663, 1)] : List FactorBlock).map factorBlockValue).prod) = 305185311208195361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_141277
      · exact prime_oneHundredFifteenDI_190157663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 305185311208195361) ^ 152592655604097680 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 61037062241639072 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 4298384664904160 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 2160191051680 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 1604906720 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_327830805790948087 : Nat.Prime 327830805790948087 := by
  apply lucas_primality 327830805790948087 (3 : ZMod 327830805790948087)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (113, 2), (139, 1), (164620993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (113, 2), (139, 1), (164620993, 1)] : List FactorBlock).map factorBlockValue).prod) = 327830805790948087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_17
      · exact prime_oneHundredFifteenDI_113
      · exact prime_oneHundredFifteenDI_139
      · exact prime_oneHundredFifteenDI_164620993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 327830805790948087) ^ 163915402895474043 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 327830805790948087) ^ 109276935263649362 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 327830805790948087) ^ 29802800526449826 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 327830805790948087) ^ 19284165046526358 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 327830805790948087) ^ 2901157573371222 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 327830805790948087) ^ 2358495005690274 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 327830805790948087) ^ 1991427702 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_439129048442351563 : Nat.Prime 439129048442351563 := by
  apply lucas_primality 439129048442351563 (3 : ZMod 439129048442351563)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (101, 1), (16963, 1), (249816299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (101, 1), (16963, 1), (249816299, 1)] : List FactorBlock).map factorBlockValue).prod) = 439129048442351563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_101
      · exact prime_oneHundredFifteenDI_16963
      · exact prime_oneHundredFifteenDI_249816299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 439129048442351563) ^ 219564524221175781 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 439129048442351563) ^ 146376349480783854 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 439129048442351563) ^ 23112055181176398 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 439129048442351563) ^ 4347812360815362 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 439129048442351563) ^ 25887463800174 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 439129048442351563) ^ 1757807838 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_490459576096940467 : Nat.Prime 490459576096940467 := by
  apply lucas_primality 490459576096940467 (2 : ZMod 490459576096940467)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (607, 1), (26573, 1), (5067837601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (607, 1), (26573, 1), (5067837601, 1)] : List FactorBlock).map factorBlockValue).prod) = 490459576096940467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_607
      · exact prime_oneHundredFifteenDI_26573
      · exact prime_oneHundredFifteenDI_5067837601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 490459576096940467) ^ 245229788048470233 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 490459576096940467) ^ 163486525365646822 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 490459576096940467) ^ 808005891428238 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 490459576096940467) ^ 18457064542842 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 490459576096940467) ^ 96778866 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_788217060554422271 : Nat.Prime 788217060554422271 := by
  apply lucas_primality 788217060554422271 (11 : ZMod 788217060554422271)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12378007, 1), (6367883461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12378007, 1), (6367883461, 1)] : List FactorBlock).map factorBlockValue).prod) = 788217060554422271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_12378007
      · exact prime_oneHundredFifteenDI_6367883461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 788217060554422271) ^ 394108530277211135 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 788217060554422271) ^ 157643412110884454 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 788217060554422271) ^ 63678834610 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (11 : ZMod 788217060554422271) ^ 123780070 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_919274401085211827 : Nat.Prime 919274401085211827 := by
  apply lucas_primality 919274401085211827 (2 : ZMod 919274401085211827)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1019, 1), (451066928893627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1019, 1), (451066928893627, 1)] : List FactorBlock).map factorBlockValue).prod) = 919274401085211827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_1019
      · exact prime_oneHundredFifteenDI_451066928893627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 919274401085211827) ^ 459637200542605913 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 919274401085211827) ^ 902133857787254 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 919274401085211827) ^ 2038 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_3525236034297377371 : Nat.Prime 3525236034297377371 := by
  apply lucas_primality 3525236034297377371 (2 : ZMod 3525236034297377371)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (68947763, 1), (1704302833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (68947763, 1), (1704302833, 1)] : List FactorBlock).map factorBlockValue).prod) = 3525236034297377371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_68947763
      · exact prime_oneHundredFifteenDI_1704302833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3525236034297377371) ^ 1762618017148688685 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3525236034297377371) ^ 1175078678099125790 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3525236034297377371) ^ 705047206859475474 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3525236034297377371) ^ 51129084990 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3525236034297377371) ^ 2068432890 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_3685425401214259987 : Nat.Prime 3685425401214259987 := by
  apply lucas_primality 3685425401214259987 (2 : ZMod 3685425401214259987)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (6332346050196323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (6332346050196323, 1)] : List FactorBlock).map factorBlockValue).prod) = 3685425401214259987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_97
      · exact prime_oneHundredFifteenDI_6332346050196323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3685425401214259987) ^ 1842712700607129993 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3685425401214259987) ^ 1228475133738086662 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3685425401214259987) ^ 37994076301177938 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3685425401214259987) ^ 582 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5568736931683450153 : Nat.Prime 5568736931683450153 := by
  apply lucas_primality 5568736931683450153 (5 : ZMod 5568736931683450153)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (41, 1), (356137, 1), (690902353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (41, 1), (356137, 1), (690902353, 1)] : List FactorBlock).map factorBlockValue).prod) = 5568736931683450153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_41
      · exact prime_oneHundredFifteenDI_356137
      · exact prime_oneHundredFifteenDI_690902353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5568736931683450153) ^ 2784368465841725076 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5568736931683450153) ^ 1856245643894483384 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5568736931683450153) ^ 242118997029715224 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5568736931683450153) ^ 135822851992279272 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5568736931683450153) ^ 15636502053096 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 5568736931683450153) ^ 8060092584 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5805811681899548393 : Nat.Prime 5805811681899548393 := by
  apply lucas_primality 5805811681899548393 (3 : ZMod 5805811681899548393)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (64180657, 1), (11307557357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (64180657, 1), (11307557357, 1)] : List FactorBlock).map factorBlockValue).prod) = 5805811681899548393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_64180657
      · exact prime_oneHundredFifteenDI_11307557357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5805811681899548393) ^ 2902905840949774196 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5805811681899548393) ^ 90460458856 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5805811681899548393) ^ 513445256 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_6077681734656833501 : Nat.Prime 6077681734656833501 := by
  apply lucas_primality 6077681734656833501 (2 : ZMod 6077681734656833501)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (787, 1), (1439, 1), (10733279119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (787, 1), (1439, 1), (10733279119, 1)] : List FactorBlock).map factorBlockValue).prod) = 6077681734656833501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_787
      · exact prime_oneHundredFifteenDI_1439
      · exact prime_oneHundredFifteenDI_10733279119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6077681734656833501) ^ 3038840867328416750 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6077681734656833501) ^ 1215536346931366700 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6077681734656833501) ^ 7722594326120500 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6077681734656833501) ^ 4223545333326500 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6077681734656833501) ^ 566246500 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_15602017149911940271 : Nat.Prime 15602017149911940271 := by
  apply lucas_primality 15602017149911940271 (3 : ZMod 15602017149911940271)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (61, 1), (13416959, 1), (33444289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (61, 1), (13416959, 1), (33444289, 1)] : List FactorBlock).map factorBlockValue).prod) = 15602017149911940271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_61
      · exact prime_oneHundredFifteenDI_13416959
      · exact prime_oneHundredFifteenDI_33444289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15602017149911940271) ^ 7801008574955970135 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 5200672383303980090 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 3120403429982388054 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 821158797363786330 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 255770772949376070 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 1162857928530 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 466507664430 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_17660765089967180327 : Nat.Prime 17660765089967180327 := by
  apply lucas_primality 17660765089967180327 (5 : ZMod 17660765089967180327)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2797, 1), (10211, 1), (309185255989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2797, 1), (10211, 1), (309185255989, 1)] : List FactorBlock).map factorBlockValue).prod) = 17660765089967180327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_2797
      · exact prime_oneHundredFifteenDI_10211
      · exact prime_oneHundredFifteenDI_309185255989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17660765089967180327) ^ 8830382544983590163 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 6314181297807358 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 1729582322002466 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 57120334 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_25137401309402306957 : Nat.Prime 25137401309402306957 := by
  apply lucas_primality 25137401309402306957 (2 : ZMod 25137401309402306957)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (1523, 1), (30118956186889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (1523, 1), (30118956186889, 1)] : List FactorBlock).map factorBlockValue).prod) = 25137401309402306957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_137
      · exact prime_oneHundredFifteenDI_1523
      · exact prime_oneHundredFifteenDI_30118956186889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25137401309402306957) ^ 12568700654701153478 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25137401309402306957) ^ 183484681090527788 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25137401309402306957) ^ 16505187990415172 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25137401309402306957) ^ 834604 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_26026180013202820837 : Nat.Prime 26026180013202820837 := by
  apply lucas_primality 26026180013202820837 (6 : ZMod 26026180013202820837)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (173, 1), (601, 1), (270905537843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (173, 1), (601, 1), (270905537843, 1)] : List FactorBlock).map factorBlockValue).prod) = 26026180013202820837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_173
      · exact prime_oneHundredFifteenDI_601
      · exact prime_oneHundredFifteenDI_270905537843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26026180013202820837) ^ 13013090006601410418 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26026180013202820837) ^ 8675393337734273612 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26026180013202820837) ^ 3718025716171831548 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26026180013202820837) ^ 2366016364836620076 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26026180013202820837) ^ 150440346897126132 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26026180013202820837) ^ 43304792035279236 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26026180013202820837) ^ 96071052 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_28923733390850689687 : Nat.Prime 28923733390850689687 := by
  apply lucas_primality 28923733390850689687 (6 : ZMod 28923733390850689687)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1097, 1), (231282552022667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1097, 1), (231282552022667, 1)] : List FactorBlock).map factorBlockValue).prod) = 28923733390850689687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_1097
      · exact prime_oneHundredFifteenDI_231282552022667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 28923733390850689687) ^ 14461866695425344843 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 28923733390850689687) ^ 9641244463616896562 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 28923733390850689687) ^ 1522301757413194194 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 28923733390850689687) ^ 26366210930584038 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 28923733390850689687) ^ 125058 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_48461861549767053209 : Nat.Prime 48461861549767053209 := by
  apply lucas_primality 48461861549767053209 (3 : ZMod 48461861549767053209)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7723, 1), (6627851, 1), (118345387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7723, 1), (6627851, 1), (118345387, 1)] : List FactorBlock).map factorBlockValue).prod) = 48461861549767053209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7723
      · exact prime_oneHundredFifteenDI_6627851
      · exact prime_oneHundredFifteenDI_118345387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 48461861549767053209) ^ 24230930774883526604 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48461861549767053209) ^ 6275004732586696 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48461861549767053209) ^ 7311851390408 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48461861549767053209) ^ 409495146184 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_2063
      · exact prime_oneHundredFifteenDI_15269
      · exact prime_oneHundredFifteenDI_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_113737432678328802067 : Nat.Prime 113737432678328802067 := by
  apply lucas_primality 113737432678328802067 (2 : ZMod 113737432678328802067)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1637, 1), (11579864862383303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1637, 1), (11579864862383303, 1)] : List FactorBlock).map factorBlockValue).prod) = 113737432678328802067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_1637
      · exact prime_oneHundredFifteenDI_11579864862383303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113737432678328802067) ^ 56868716339164401033 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 113737432678328802067) ^ 37912477559442934022 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 113737432678328802067) ^ 69479189174299818 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 113737432678328802067) ^ 9822 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_285162734706916490807 : Nat.Prime 285162734706916490807 := by
  apply lucas_primality 285162734706916490807 (5 : ZMod 285162734706916490807)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (1523, 1), (3917, 1), (10597, 1), (7346627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (1523, 1), (3917, 1), (10597, 1), (7346627, 1)] : List FactorBlock).map factorBlockValue).prod) = 285162734706916490807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_307
      · exact prime_oneHundredFifteenDI_1523
      · exact prime_oneHundredFifteenDI_3917
      · exact prime_oneHundredFifteenDI_10597
      · exact prime_oneHundredFifteenDI_7346627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 285162734706916490807) ^ 142581367353458245403 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 285162734706916490807) ^ 928868842693539058 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 285162734706916490807) ^ 187237514581035122 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 285162734706916490807) ^ 72801310877435918 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 285162734706916490807) ^ 26909760753695998 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 285162734706916490807) ^ 38815463845778 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_286491562672172902459 : Nat.Prime 286491562672172902459 := by
  apply lucas_primality 286491562672172902459 (2 : ZMod 286491562672172902459)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (487, 1), (1010787564908137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (487, 1), (1010787564908137, 1)] : List FactorBlock).map factorBlockValue).prod) = 286491562672172902459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_97
      · exact prime_oneHundredFifteenDI_487
      · exact prime_oneHundredFifteenDI_1010787564908137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 286491562672172902459) ^ 143245781336086451229 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 286491562672172902459) ^ 95497187557390967486 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 286491562672172902459) ^ 2953521264661576314 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 286491562672172902459) ^ 588278362776535734 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 286491562672172902459) ^ 283434 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_957822752249553426317 : Nat.Prime 957822752249553426317 := by
  apply lucas_primality 957822752249553426317 (2 : ZMod 957822752249553426317)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (5568736931683450153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (5568736931683450153, 1)] : List FactorBlock).map factorBlockValue).prod) = 957822752249553426317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_43
      · exact prime_oneHundredFifteenDI_5568736931683450153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 957822752249553426317) ^ 478911376124776713158 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 957822752249553426317) ^ 22274947726733800612 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 957822752249553426317) ^ 172 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_71
      · exact prime_oneHundredFifteenDI_199
      · exact prime_oneHundredFifteenDI_52864081
      · exact prime_oneHundredFifteenDI_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1216651170656360899459 : Nat.Prime 1216651170656360899459 := by
  apply lucas_primality 1216651170656360899459 (2 : ZMod 1216651170656360899459)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1409, 1), (47971420655167609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1409, 1), (47971420655167609, 1)] : List FactorBlock).map factorBlockValue).prod) = 1216651170656360899459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_1409
      · exact prime_oneHundredFifteenDI_47971420655167609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1216651170656360899459) ^ 608325585328180449729 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1216651170656360899459) ^ 405550390218786966486 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1216651170656360899459) ^ 863485571793016962 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1216651170656360899459) ^ 25362 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2337413551456172853497 : Nat.Prime 2337413551456172853497 := by
  apply lucas_primality 2337413551456172853497 (3 : ZMod 2337413551456172853497)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (257, 1), (162410613636476713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (257, 1), (162410613636476713, 1)] : List FactorBlock).map factorBlockValue).prod) = 2337413551456172853497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_257
      · exact prime_oneHundredFifteenDI_162410613636476713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2337413551456172853497) ^ 1168706775728086426748 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2337413551456172853497) ^ 333916221636596121928 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2337413551456172853497) ^ 9094994363642695928 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2337413551456172853497) ^ 14392 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2539860848461355402359 : Nat.Prime 2539860848461355402359 := by
  apply lucas_primality 2539860848461355402359 (6 : ZMod 2539860848461355402359)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (131, 1), (9851, 1), (2542830126457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (131, 1), (9851, 1), (2542830126457, 1)] : List FactorBlock).map factorBlockValue).prod) = 2539860848461355402359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_43
      · exact prime_oneHundredFifteenDI_131
      · exact prime_oneHundredFifteenDI_9851
      · exact prime_oneHundredFifteenDI_2542830126457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2539860848461355402359) ^ 1269930424230677701179 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2539860848461355402359) ^ 846620282820451800786 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2539860848461355402359) ^ 59066531359566404706 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2539860848461355402359) ^ 19388250751613400018 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2539860848461355402359) ^ 257827717841981058 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 2539860848461355402359) ^ 998832294 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_3568068543723551863573 : Nat.Prime 3568068543723551863573 := by
  apply lucas_primality 3568068543723551863573 (2 : ZMod 3568068543723551863573)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2690351, 1), (110520540000281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2690351, 1), (110520540000281, 1)] : List FactorBlock).map factorBlockValue).prod) = 3568068543723551863573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_2690351
      · exact prime_oneHundredFifteenDI_110520540000281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3568068543723551863573) ^ 1784034271861775931786 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3568068543723551863573) ^ 1189356181241183954524 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3568068543723551863573) ^ 1326246480003372 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3568068543723551863573) ^ 32284212 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_7839188574989943285743 : Nat.Prime 7839188574989943285743 := by
  apply lucas_primality 7839188574989943285743 (5 : ZMod 7839188574989943285743)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (149, 1), (1602697, 1), (565985657183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (149, 1), (1602697, 1), (565985657183, 1)] : List FactorBlock).map factorBlockValue).prod) = 7839188574989943285743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_29
      · exact prime_oneHundredFifteenDI_149
      · exact prime_oneHundredFifteenDI_1602697
      · exact prime_oneHundredFifteenDI_565985657183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7839188574989943285743) ^ 3919594287494971642871 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7839188574989943285743) ^ 270316847413446320198 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7839188574989943285743) ^ 52612003858992907958 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7839188574989943285743) ^ 4891248049375486 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7839188574989943285743) ^ 13850507474 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_9529073139176856494459 : Nat.Prime 9529073139176856494459 := by
  apply lucas_primality 9529073139176856494459 (6 : ZMod 9529073139176856494459)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (57139, 1), (2033780937964471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (57139, 1), (2033780937964471, 1)] : List FactorBlock).map factorBlockValue).prod) = 9529073139176856494459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_41
      · exact prime_oneHundredFifteenDI_57139
      · exact prime_oneHundredFifteenDI_2033780937964471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 9529073139176856494459) ^ 4764536569588428247229 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9529073139176856494459) ^ 232416418028703816938 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9529073139176856494459) ^ 166770036913086622 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9529073139176856494459) ^ 4685398 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_10476249422528165885419 : Nat.Prime 10476249422528165885419 := by
  apply lucas_primality 10476249422528165885419 (2 : ZMod 10476249422528165885419)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (2819, 1), (10111, 1), (1976076253357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (2819, 1), (10111, 1), (1976076253357, 1)] : List FactorBlock).map factorBlockValue).prod) = 10476249422528165885419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_2819
      · exact prime_oneHundredFifteenDI_10111
      · exact prime_oneHundredFifteenDI_1976076253357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10476249422528165885419) ^ 5238124711264082942709 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10476249422528165885419) ^ 3492083140842721961806 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10476249422528165885419) ^ 337943529758973093078 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10476249422528165885419) ^ 3716299901570828622 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10476249422528165885419) ^ 1036123966227689238 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10476249422528165885419) ^ 5301541074 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_19391065960070321374877 : Nat.Prime 19391065960070321374877 := by
  apply lucas_primality 19391065960070321374877 (2 : ZMod 19391065960070321374877)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (285162734706916490807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (285162734706916490807, 1)] : List FactorBlock).map factorBlockValue).prod) = 19391065960070321374877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_17
      · exact prime_oneHundredFifteenDI_285162734706916490807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19391065960070321374877) ^ 9695532980035160687438 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 19391065960070321374877) ^ 1140650938827665963228 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 19391065960070321374877) ^ 68 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_21500316536914473447941 : Nat.Prime 21500316536914473447941 := by
  apply lucas_primality 21500316536914473447941 (2 : ZMod 21500316536914473447941)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59, 1), (281, 1), (707827, 1), (91607156309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59, 1), (281, 1), (707827, 1), (91607156309, 1)] : List FactorBlock).map factorBlockValue).prod) = 21500316536914473447941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_59
      · exact prime_oneHundredFifteenDI_281
      · exact prime_oneHundredFifteenDI_707827
      · exact prime_oneHundredFifteenDI_91607156309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21500316536914473447941) ^ 10750158268457236723970 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 4300063307382894689588 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 364412144693465651660 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 76513581981902040740 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 30375100888938220 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 234701276660 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_63230061040149014564701 : Nat.Prime 63230061040149014564701 := by
  apply lucas_primality 63230061040149014564701 (13 : ZMod 63230061040149014564701)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 2), (15101, 1), (1562713, 1), (182272577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 2), (15101, 1), (1562713, 1), (182272577, 1)] : List FactorBlock).map factorBlockValue).prod) = 63230061040149014564701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_15101
      · exact prime_oneHundredFifteenDI_1562713
      · exact prime_oneHundredFifteenDI_182272577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 63230061040149014564701) ^ 31615030520074507282350 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 63230061040149014564701) ^ 21076687013383004854900 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 63230061040149014564701) ^ 12646012208029802912940 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 63230061040149014564701) ^ 9032865862878430652100 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 63230061040149014564701) ^ 4187143966634594700 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 63230061040149014564701) ^ 40461723323571900 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (13 : ZMod 63230061040149014564701) ^ 346898376491100 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_66963966748602008299927 : Nat.Prime 66963966748602008299927 := by
  apply lucas_primality 66963966748602008299927 (3 : ZMod 66963966748602008299927)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (3314141, 1), (30895301819009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (3314141, 1), (30895301819009, 1)] : List FactorBlock).map factorBlockValue).prod) = 66963966748602008299927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_109
      · exact prime_oneHundredFifteenDI_3314141
      · exact prime_oneHundredFifteenDI_30895301819009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66963966748602008299927) ^ 33481983374301004149963 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66963966748602008299927) ^ 22321322249534002766642 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66963966748602008299927) ^ 614348318794513837614 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66963966748602008299927) ^ 20205527389631886 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66963966748602008299927) ^ 2167448214 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_68238834541154181621887 : Nat.Prime 68238834541154181621887 := by
  apply lucas_primality 68238834541154181621887 (5 : ZMod 68238834541154181621887)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (127, 1), (11720081, 1), (1763290707253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (127, 1), (11720081, 1), (1763290707253, 1)] : List FactorBlock).map factorBlockValue).prod) = 68238834541154181621887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_127
      · exact prime_oneHundredFifteenDI_11720081
      · exact prime_oneHundredFifteenDI_1763290707253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68238834541154181621887) ^ 34119417270577090810943 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68238834541154181621887) ^ 5249141118550321663222 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68238834541154181621887) ^ 537313657804363634818 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68238834541154181621887) ^ 5822385915349406 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68238834541154181621887) ^ 38699707462 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_68475561093742233413953 : Nat.Prime 68475561093742233413953 := by
  apply lucas_primality 68475561093742233413953 (5 : ZMod 68475561093742233413953)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (23, 1), (103, 1), (269, 1), (3907, 1), (15915896617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (23, 1), (103, 1), (269, 1), (3907, 1), (15915896617, 1)] : List FactorBlock).map factorBlockValue).prod) = 68475561093742233413953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_103
      · exact prime_oneHundredFifteenDI_269
      · exact prime_oneHundredFifteenDI_3907
      · exact prime_oneHundredFifteenDI_15915896617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68475561093742233413953) ^ 34237780546871116706976 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68475561093742233413953) ^ 22825187031247411137984 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68475561093742233413953) ^ 2977198308423575365824 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68475561093742233413953) ^ 664811272754778965184 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68475561093742233413953) ^ 254555989196067782208 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68475561093742233413953) ^ 17526378575311551936 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 68475561093742233413953) ^ 4302337640256 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_71116103756917951266053 : Nat.Prime 71116103756917951266053 := by
  apply lucas_primality 71116103756917951266053 (2 : ZMod 71116103756917951266053)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2539860848461355402359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2539860848461355402359, 1)] : List FactorBlock).map factorBlockValue).prod) = 71116103756917951266053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_2539860848461355402359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71116103756917951266053) ^ 35558051878458975633026 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 71116103756917951266053) ^ 10159443393845421609436 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 71116103756917951266053) ^ 28 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_79058956464196627139603 : Nat.Prime 79058956464196627139603 := by
  apply lucas_primality 79058956464196627139603 (2 : ZMod 79058956464196627139603)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1579, 1), (15787, 1), (4320223, 1), (367056719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1579, 1), (15787, 1), (4320223, 1), (367056719, 1)] : List FactorBlock).map factorBlockValue).prod) = 79058956464196627139603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_1579
      · exact prime_oneHundredFifteenDI_15787
      · exact prime_oneHundredFifteenDI_4320223
      · exact prime_oneHundredFifteenDI_367056719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79058956464196627139603) ^ 39529478232098313569801 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79058956464196627139603) ^ 50069003460542512438 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79058956464196627139603) ^ 5007851806182088246 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79058956464196627139603) ^ 18299739727369774 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 79058956464196627139603) ^ 215386212462158 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_105779808321228349065217 : Nat.Prime 105779808321228349065217 := by
  apply lucas_primality 105779808321228349065217 (7 : ZMod 105779808321228349065217)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 2), (30937, 1), (185503503650249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 2), (30937, 1), (185503503650249, 1)] : List FactorBlock).map factorBlockValue).prod) = 105779808321228349065217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_30937
      · exact prime_oneHundredFifteenDI_185503503650249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 105779808321228349065217) ^ 52889904160614174532608 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 105779808321228349065217) ^ 35259936107076116355072 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 105779808321228349065217) ^ 3419200579281389568 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 105779808321228349065217) ^ 570230784 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_189020163816398040244861 : Nat.Prime 189020163816398040244861 := by
  apply lucas_primality 189020163816398040244861 (2 : ZMod 189020163816398040244861)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (211, 1), (44627389, 1), (2811421681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (211, 1), (44627389, 1), (2811421681, 1)] : List FactorBlock).map factorBlockValue).prod) = 189020163816398040244861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_17
      · exact prime_oneHundredFifteenDI_211
      · exact prime_oneHundredFifteenDI_44627389
      · exact prime_oneHundredFifteenDI_2811421681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 189020163816398040244861) ^ 94510081908199020122430 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189020163816398040244861) ^ 63006721272132680081620 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189020163816398040244861) ^ 37804032763279608048972 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189020163816398040244861) ^ 27002880545199720034980 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189020163816398040244861) ^ 11118833165670472955580 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189020163816398040244861) ^ 895830160267289290260 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189020163816398040244861) ^ 4235519219293740 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 189020163816398040244861) ^ 67232946624060 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_296363035617059270482877 : Nat.Prime 296363035617059270482877 := by
  apply lucas_primality 296363035617059270482877 (2 : ZMod 296363035617059270482877)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (431, 1), (919274401085211827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (431, 1), (919274401085211827, 1)] : List FactorBlock).map factorBlockValue).prod) = 296363035617059270482877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_17
      · exact prime_oneHundredFifteenDI_431
      · exact prime_oneHundredFifteenDI_919274401085211827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 296363035617059270482877) ^ 148181517808529635241438 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 296363035617059270482877) ^ 26942094147005388225716 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 296363035617059270482877) ^ 17433119742179957087228 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 296363035617059270482877) ^ 687617252011738446596 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 296363035617059270482877) ^ 322388 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_347036805909051547730863 : Nat.Prime 347036805909051547730863 := by
  apply lucas_primality 347036805909051547730863 (3 : ZMod 347036805909051547730863)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (5928970109, 1), (86330962481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (5928970109, 1), (86330962481, 1)] : List FactorBlock).map factorBlockValue).prod) = 347036805909051547730863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_113
      · exact prime_oneHundredFifteenDI_5928970109
      · exact prime_oneHundredFifteenDI_86330962481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 347036805909051547730863) ^ 173518402954525773865431 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 347036805909051547730863) ^ 115678935303017182576954 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 347036805909051547730863) ^ 3071122176186296882574 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 347036805909051547730863) ^ 58532392562118 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 347036805909051547730863) ^ 4019841733902 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_495799769064908666838569 : Nat.Prime 495799769064908666838569 := by
  apply lucas_primality 495799769064908666838569 (3 : ZMod 495799769064908666838569)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (19, 1), (557, 1), (4127, 1), (11727020864261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (19, 1), (557, 1), (4127, 1), (11727020864261, 1)] : List FactorBlock).map factorBlockValue).prod) = 495799769064908666838569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_19
      · exact prime_oneHundredFifteenDI_557
      · exact prime_oneHundredFifteenDI_4127
      · exact prime_oneHundredFifteenDI_11727020864261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 495799769064908666838569) ^ 247899884532454333419284 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 45072706278628060621688 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 26094724687626771938872 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 890125258644360263624 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 120135635828666989784 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 42278407688 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_702207384976807953577937 : Nat.Prime 702207384976807953577937 := by
  apply lucas_primality 702207384976807953577937 (3 : ZMod 702207384976807953577937)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (248828897, 1), (25196867687099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (248828897, 1), (25196867687099, 1)] : List FactorBlock).map factorBlockValue).prod) = 702207384976807953577937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_248828897
      · exact prime_oneHundredFifteenDI_25196867687099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 702207384976807953577937) ^ 351103692488403976788968 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 702207384976807953577937) ^ 100315340710972564796848 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 702207384976807953577937) ^ 2822049180955088 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 702207384976807953577937) ^ 27868836464 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_2677498408236172023155371 : Nat.Prime 2677498408236172023155371 := by
  apply lucas_primality 2677498408236172023155371 (2 : ZMod 2677498408236172023155371)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (397, 1), (3685425401214259987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (397, 1), (3685425401214259987, 1)] : List FactorBlock).map factorBlockValue).prod) = 2677498408236172023155371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_61
      · exact prime_oneHundredFifteenDI_397
      · exact prime_oneHundredFifteenDI_3685425401214259987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2677498408236172023155371) ^ 1338749204118086011577685 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677498408236172023155371) ^ 892499469412057341051790 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677498408236172023155371) ^ 535499681647234404631074 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677498408236172023155371) ^ 43893416528461836445170 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677498408236172023155371) ^ 6744328484222095776210 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2677498408236172023155371) ^ 726510 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_3270172495473941195973797 : Nat.Prime 3270172495473941195973797 := by
  apply lucas_primality 3270172495473941195973797 (2 : ZMod 3270172495473941195973797)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (276239, 1), (227657689918035107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (276239, 1), (227657689918035107, 1)] : List FactorBlock).map factorBlockValue).prod) = 3270172495473941195973797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_276239
      · exact prime_oneHundredFifteenDI_227657689918035107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3270172495473941195973797) ^ 1635086247736970597986898 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3270172495473941195973797) ^ 251551730421072399690292 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3270172495473941195973797) ^ 11838199875737825564 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3270172495473941195973797) ^ 14364428 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_5292564586859145126856109 : Nat.Prime 5292564586859145126856109 := by
  apply lucas_primality 5292564586859145126856109 (2 : ZMod 5292564586859145126856109)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (189020163816398040244861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (189020163816398040244861, 1)] : List FactorBlock).map factorBlockValue).prod) = 5292564586859145126856109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_189020163816398040244861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5292564586859145126856109) ^ 2646282293429572563428054 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5292564586859145126856109) ^ 756080655265592160979444 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5292564586859145126856109) ^ 28 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_14839630175924970439184303 : Nat.Prime 14839630175924970439184303 := by
  apply lucas_primality 14839630175924970439184303 (5 : ZMod 14839630175924970439184303)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (37, 1), (12281, 1), (1938301, 1), (271753228993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (37, 1), (12281, 1), (1938301, 1), (271753228993, 1)] : List FactorBlock).map factorBlockValue).prod) = 14839630175924970439184303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_31
      · exact prime_oneHundredFifteenDI_37
      · exact prime_oneHundredFifteenDI_12281
      · exact prime_oneHundredFifteenDI_1938301
      · exact prime_oneHundredFifteenDI_271753228993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14839630175924970439184303) ^ 7419815087962485219592151 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14839630175924970439184303) ^ 478697747610482917393042 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14839630175924970439184303) ^ 401071085835810011869846 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14839630175924970439184303) ^ 1208340540340767888542 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14839630175924970439184303) ^ 7655998823673397702 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14839630175924970439184303) ^ 54607005888814 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_24648421260301772872336219 : Nat.Prime 24648421260301772872336219 := by
  apply lucas_primality 24648421260301772872336219 (2 : ZMod 24648421260301772872336219)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (397, 1), (43669, 1), (87121, 1), (21084414319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (397, 1), (43669, 1), (87121, 1), (21084414319, 1)] : List FactorBlock).map factorBlockValue).prod) = 24648421260301772872336219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_43
      · exact prime_oneHundredFifteenDI_397
      · exact prime_oneHundredFifteenDI_43669
      · exact prime_oneHundredFifteenDI_87121
      · exact prime_oneHundredFifteenDI_21084414319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24648421260301772872336219) ^ 12324210630150886436168109 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24648421260301772872336219) ^ 8216140420100590957445406 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24648421260301772872336219) ^ 573219099076785415635726 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24648421260301772872336219) ^ 62086703426452828393794 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24648421260301772872336219) ^ 564437501667127089522 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24648421260301772872336219) ^ 282921698101511379258 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 24648421260301772872336219) ^ 1169035140714822 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_33545692492431428365113887 : Nat.Prime 33545692492431428365113887 := by
  apply lucas_primality 33545692492431428365113887 (5 : ZMod 33545692492431428365113887)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (223, 1), (797, 1), (109279, 1), (10931500474933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (223, 1), (797, 1), (109279, 1), (10931500474933, 1)] : List FactorBlock).map factorBlockValue).prod) = 33545692492431428365113887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_79
      · exact prime_oneHundredFifteenDI_223
      · exact prime_oneHundredFifteenDI_797
      · exact prime_oneHundredFifteenDI_109279
      · exact prime_oneHundredFifteenDI_10931500474933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33545692492431428365113887) ^ 16772846246215714182556943 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33545692492431428365113887) ^ 424629018891537067912834 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33545692492431428365113887) ^ 150429114315836001637282 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33545692492431428365113887) ^ 42089952939060763318838 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33545692492431428365113887) ^ 306972908723830089634 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33545692492431428365113887) ^ 3068718019942 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_38406975048538016712939713 : Nat.Prime 38406975048538016712939713 := by
  apply lucas_primality 38406975048538016712939713 (3 : ZMod 38406975048538016712939713)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (411211963949, 1), (1459366549967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (411211963949, 1), (1459366549967, 1)] : List FactorBlock).map factorBlockValue).prod) = 38406975048538016712939713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_411211963949
      · exact prime_oneHundredFifteenDI_1459366549967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38406975048538016712939713) ^ 19203487524269008356469856 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 38406975048538016712939713) ^ 93399459197888 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 38406975048538016712939713) ^ 26317565692736 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_51558851600995289785288807 : Nat.Prime 51558851600995289785288807 := by
  apply lucas_primality 51558851600995289785288807 (3 : ZMod 51558851600995289785288807)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (8053, 1), (26026180013202820837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (8053, 1), (26026180013202820837, 1)] : List FactorBlock).map factorBlockValue).prod) = 51558851600995289785288807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_41
      · exact prime_oneHundredFifteenDI_8053
      · exact prime_oneHundredFifteenDI_26026180013202820837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51558851600995289785288807) ^ 25779425800497644892644403 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 51558851600995289785288807) ^ 17186283866998429928429602 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 51558851600995289785288807) ^ 1257532965877933897202166 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 51558851600995289785288807) ^ 6402440283247893925902 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 51558851600995289785288807) ^ 1981038 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_147143605705437856237885913 : Nat.Prime 147143605705437856237885913 := by
  apply lucas_primality 147143605705437856237885913 (3 : ZMod 147143605705437856237885913)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (347036805909051547730863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (347036805909051547730863, 1)] : List FactorBlock).map factorBlockValue).prod) = 147143605705437856237885913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_53
      · exact prime_oneHundredFifteenDI_347036805909051547730863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 147143605705437856237885913) ^ 73571802852718928118942956 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 147143605705437856237885913) ^ 2776294447272412381846904 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 147143605705437856237885913) ^ 424 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_222157992927817939810141477 : Nat.Prime 222157992927817939810141477 := by
  apply lucas_primality 222157992927817939810141477 (5 : ZMod 222157992927817939810141477)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (59, 1), (139, 1), (199, 1), (8369, 1), (1696811, 1), (88758767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (59, 1), (139, 1), (199, 1), (8369, 1), (1696811, 1), (88758767, 1)] : List FactorBlock).map factorBlockValue).prod) = 222157992927817939810141477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_59
      · exact prime_oneHundredFifteenDI_139
      · exact prime_oneHundredFifteenDI_199
      · exact prime_oneHundredFifteenDI_8369
      · exact prime_oneHundredFifteenDI_1696811
      · exact prime_oneHundredFifteenDI_88758767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 222157992927817939810141477) ^ 111078996463908969905070738 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 222157992927817939810141477) ^ 74052664309272646603380492 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 222157992927817939810141477) ^ 3765389710640982030680364 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 222157992927817939810141477) ^ 1598258941926747768418284 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 222157992927817939810141477) ^ 1116371823757879094523324 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 222157992927817939810141477) ^ 26545345074419636732004 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 222157992927817939810141477) ^ 130926775538240817516 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 222157992927817939810141477) ^ 2502941404400288028 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_294287211410875712475771827 : Nat.Prime 294287211410875712475771827 := by
  apply lucas_primality 294287211410875712475771827 (2 : ZMod 294287211410875712475771827)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (147143605705437856237885913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (147143605705437856237885913, 1)] : List FactorBlock).map factorBlockValue).prod) = 294287211410875712475771827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_147143605705437856237885913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 294287211410875712475771827) ^ 147143605705437856237885913 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 294287211410875712475771827) ^ 2 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_385157766775707023126930833 : Nat.Prime 385157766775707023126930833 := by
  apply lucas_primality 385157766775707023126930833 (5 : ZMod 385157766775707023126930833)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (57549366421, 1), (19918601169697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (57549366421, 1), (19918601169697, 1)] : List FactorBlock).map factorBlockValue).prod) = 385157766775707023126930833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_57549366421
      · exact prime_oneHundredFifteenDI_19918601169697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 385157766775707023126930833) ^ 192578883387853511563465416 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 385157766775707023126930833) ^ 128385922258569007708976944 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 385157766775707023126930833) ^ 55022538110815289018132976 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 385157766775707023126930833) ^ 6692649993018192 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 385157766775707023126930833) ^ 19336587117456 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_531096451843064762358619469 : Nat.Prime 531096451843064762358619469 := by
  apply lucas_primality 531096451843064762358619469 (2 : ZMod 531096451843064762358619469)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (277, 1), (68475561093742233413953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (277, 1), (68475561093742233413953, 1)] : List FactorBlock).map factorBlockValue).prod) = 531096451843064762358619469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_277
      · exact prime_oneHundredFifteenDI_68475561093742233413953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 531096451843064762358619469) ^ 265548225921532381179309734 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531096451843064762358619469) ^ 75870921691866394622659924 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531096451843064762358619469) ^ 1917315710624782535590684 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531096451843064762358619469) ^ 7756 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_888631971711271759240565909 : Nat.Prime 888631971711271759240565909 := by
  apply lucas_primality 888631971711271759240565909 (2 : ZMod 888631971711271759240565909)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (222157992927817939810141477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (222157992927817939810141477, 1)] : List FactorBlock).map factorBlockValue).prod) = 888631971711271759240565909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_222157992927817939810141477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 888631971711271759240565909) ^ 444315985855635879620282954 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 888631971711271759240565909) ^ 4 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_1346145462097273061027787961 : Nat.Prime 1346145462097273061027787961 := by
  apply lucas_primality 1346145462097273061027787961 (14 : ZMod 1346145462097273061027787961)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (53, 1), (7839188574989943285743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (53, 1), (7839188574989943285743, 1)] : List FactorBlock).map factorBlockValue).prod) = 1346145462097273061027787961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_53
      · exact prime_oneHundredFifteenDI_7839188574989943285743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1346145462097273061027787961) ^ 673072731048636530513893980 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1346145462097273061027787961) ^ 448715154032424353675929320 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1346145462097273061027787961) ^ 269229092419454612205557592 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1346145462097273061027787961) ^ 25398970982967416245807320 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1346145462097273061027787961) ^ 171720 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_8497543229489036197737911501 : Nat.Prime 8497543229489036197737911501 := by
  apply lucas_primality 8497543229489036197737911501 (2 : ZMod 8497543229489036197737911501)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (23, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (23, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 8497543229489036197737911501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_23
      · exact prime_oneHundredFifteenDI_171401
      · exact prime_oneHundredFifteenDI_714027719
      · exact prime_oneHundredFifteenDI_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8497543229489036197737911501) ^ 4248771614744518098868955750 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8497543229489036197737911501) ^ 1699508645897807239547582300 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8497543229489036197737911501) ^ 369458401282132008597300500 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8497543229489036197737911501) ^ 49576975802294246811500 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8497543229489036197737911501) ^ 11900859033021708500 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8497543229489036197737911501) ^ 1407428248239668500 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_10458514743986506089523583387 : Nat.Prime 10458514743986506089523583387 := by
  apply lucas_primality 10458514743986506089523583387 (2 : ZMod 10458514743986506089523583387)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (120976789, 1), (865679951, 1), (1019024263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (120976789, 1), (865679951, 1), (1019024263, 1)] : List FactorBlock).map factorBlockValue).prod) = 10458514743986506089523583387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_7
      · exact prime_oneHundredFifteenDI_120976789
      · exact prime_oneHundredFifteenDI_865679951
      · exact prime_oneHundredFifteenDI_1019024263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10458514743986506089523583387) ^ 5229257371993253044761791693 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10458514743986506089523583387) ^ 1494073534855215155646226198 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10458514743986506089523583387) ^ 86450589658041809074 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10458514743986506089523583387) ^ 12081271758581487686 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10458514743986506089523583387) ^ 10263263715818419222 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_13596069167182457916380658409 : Nat.Prime 13596069167182457916380658409 := by
  apply lucas_primality 13596069167182457916380658409 (7 : ZMod 13596069167182457916380658409)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (160699277, 1), (3525236034297377371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (160699277, 1), (3525236034297377371, 1)] : List FactorBlock).map factorBlockValue).prod) = 13596069167182457916380658409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_160699277
      · exact prime_oneHundredFifteenDI_3525236034297377371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 13596069167182457916380658409) ^ 6798034583591228958190329204 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 13596069167182457916380658409) ^ 4532023055727485972126886136 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 13596069167182457916380658409) ^ 84605664823137056904 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (7 : ZMod 13596069167182457916380658409) ^ 3856782648 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_19422955953117797023400940583 : Nat.Prime 19422955953117797023400940583 := by
  apply lucas_primality 19422955953117797023400940583 (5 : ZMod 19422955953117797023400940583)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (294287211410875712475771827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (294287211410875712475771827, 1)] : List FactorBlock).map factorBlockValue).prod) = 19422955953117797023400940583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_294287211410875712475771827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19422955953117797023400940583) ^ 9711477976558898511700470291 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19422955953117797023400940583) ^ 6474318651039265674466980194 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19422955953117797023400940583) ^ 1765723268465254274854630962 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (5 : ZMod 19422955953117797023400940583) ^ 66 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_27192138334364915832761316803 : Nat.Prime 27192138334364915832761316803 := by
  apply lucas_primality 27192138334364915832761316803 (2 : ZMod 27192138334364915832761316803)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364915832761316803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_10979
      · exact prime_oneHundredFifteenDI_15149
      · exact prime_oneHundredFifteenDI_63029
      · exact prime_oneHundredFifteenDI_9642827
      · exact prime_oneHundredFifteenDI_134499857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27192138334364915832761316803) ^ 13596069167182457916380658401 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 2476740899386548486452438 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 1794979096598119732837898 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 431422652023115007897338 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 2819934271802752017926 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 202172247174693396386 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_45320230557274859721268861339 : Nat.Prime 45320230557274859721268861339 := by
  apply lucas_primality 45320230557274859721268861339 (2 : ZMod 45320230557274859721268861339)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31847, 1), (79058956464196627139603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31847, 1), (79058956464196627139603, 1)] : List FactorBlock).map factorBlockValue).prod) = 45320230557274859721268861339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_31847
      · exact prime_oneHundredFifteenDI_79058956464196627139603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45320230557274859721268861339) ^ 22660115278637429860634430669 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45320230557274859721268861339) ^ 15106743519091619907089620446 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45320230557274859721268861339) ^ 1423061216355539288512854 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45320230557274859721268861339) ^ 573246 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_135960691671824579163806584051 : Nat.Prime 135960691671824579163806584051 := by
  apply lucas_primality 135960691671824579163806584051 (2 : ZMod 135960691671824579163806584051)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (1289, 1), (1723669, 1), (135985957393556749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (1289, 1), (1723669, 1), (135985957393556749, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_3
      · exact prime_oneHundredFifteenDI_5
      · exact prime_oneHundredFifteenDI_1289
      · exact prime_oneHundredFifteenDI_1723669
      · exact prime_oneHundredFifteenDI_135985957393556749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135960691671824579163806584051) ^ 67980345835912289581903292025 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135960691671824579163806584051) ^ 45320230557274859721268861350 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135960691671824579163806584051) ^ 27192138334364915832761316810 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135960691671824579163806584051) ^ 105477650637567555596436450 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135960691671824579163806584051) ^ 78878654586132592257450 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (2 : ZMod 135960691671824579163806584051) ^ 999814203450 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem prime_oneHundredFifteenDI_135960691671824579163806584097 : Nat.Prime 135960691671824579163806584097 := by
  apply lucas_primality 135960691671824579163806584097 (3 : ZMod 135960691671824579163806584097)
  · rw [← oneHundredFifteenDIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (13, 1), (29, 1), (22480327, 1), (45575005254974837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (13, 1), (29, 1), (22480327, 1), (45575005254974837, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFifteenDI_2
      · exact prime_oneHundredFifteenDI_11
      · exact prime_oneHundredFifteenDI_13
      · exact prime_oneHundredFifteenDI_29
      · exact prime_oneHundredFifteenDI_22480327
      · exact prime_oneHundredFifteenDI_45575005254974837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 135960691671824579163806584097) ^ 67980345835912289581903292048 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135960691671824579163806584097) ^ 12360062879256779923982416736 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135960691671824579163806584097) ^ 10458514743986506089523583392 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135960691671824579163806584097) ^ 4688299712821537212545054624 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135960691671824579163806584097) ^ 6047985497356180769248 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide
    · change (3 : ZMod 135960691671824579163806584097) ^ 2983229314208 ≠ 1
      rw [← oneHundredFifteenDIFastPow_eq_pow]
      decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584000 : Nat.totient 135960691671824579163806584000 = 52019439321742061608074240000 := by
  rw [← show ((([(2, 6), (5, 3), (23, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_23, prime_oneHundredFifteenDI_171401, prime_oneHundredFifteenDI_714027719, prime_oneHundredFifteenDI_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584001 : Nat.totient 135960691671824579163806584001 = 135960690714001826914111210032 := by
  rw [← show ((([(141947653, 1), (957822752249553426317, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_141947653, prime_oneHundredFifteenDI_957822752249553426317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584002 : Nat.totient 135960691671824579163806584002 = 45320230460351136620799581792 := by
  rw [← show ((([(2, 1), (3, 1), (467586563, 1), (48461861549767053209, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_467586563, prime_oneHundredFifteenDI_48461861549767053209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584003 : Nat.totient 135960691671824579163806584003 = 135959989464439602355852812448 := by
  rw [← show ((([(193619, 1), (702207384976807953577937, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_193619, prime_oneHundredFifteenDI_702207384976807953577937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584004 : Nat.totient 135960691671824579163806584004 = 57973086804229769795734784736 := by
  rw [← show ((([(2, 2), (7, 1), (197, 1), (24648421260301772872336219, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_197, prime_oneHundredFifteenDI_24648421260301772872336219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584005 : Nat.totient 135960691671824579163806584005 = 65071345408751449213641216000 := by
  rw [← show ((([(3, 2), (5, 1), (13, 1), (41, 1), (421, 1), (863, 1), (15602017149911940271, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_13, prime_oneHundredFifteenDI_41, prime_oneHundredFifteenDI_421, prime_oneHundredFifteenDI_863, prime_oneHundredFifteenDI_15602017149911940271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584006 : Nat.totient 135960691671824579163806584006 = 67743081725847774394949369856 := by
  rw [← show ((([(2, 1), (337, 1), (1907, 1), (105779808321228349065217, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_337, prime_oneHundredFifteenDI_1907, prime_oneHundredFifteenDI_105779808321228349065217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584007 : Nat.totient 135960691671824579163806584007 = 128442005244564275563193664000 := by
  rw [← show ((([(31, 1), (71, 1), (139, 1), (373, 1), (115399, 1), (2540011, 1), (4064733229, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_31, prime_oneHundredFifteenDI_71, prime_oneHundredFifteenDI_139, prime_oneHundredFifteenDI_373, prime_oneHundredFifteenDI_115399, prime_oneHundredFifteenDI_2540011, prime_oneHundredFifteenDI_4064733229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584008 : Nat.totient 135960691671824579163806584008 = 39028258263244837913988480000 := by
  rw [← show ((([(2, 3), (3, 1), (11, 1), (19, 1), (11239, 1), (964661, 1), (6728947, 1), (371540651, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_19, prime_oneHundredFifteenDI_11239, prime_oneHundredFifteenDI_964661, prime_oneHundredFifteenDI_6728947, prime_oneHundredFifteenDI_371540651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584009 : Nat.totient 135960691671824579163806584009 = 122350967262760116770107787520 := by
  rw [← show ((([(17, 1), (29, 1), (103, 1), (2677498408236172023155371, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_17, prime_oneHundredFifteenDI_29, prime_oneHundredFifteenDI_103, prime_oneHundredFifteenDI_2677498408236172023155371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584010 : Nat.totient 135960691671824579163806584010 = 54374864802792827458860986368 := by
  rw [← show ((([(2, 1), (5, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_10979, prime_oneHundredFifteenDI_15149, prime_oneHundredFifteenDI_63029, prime_oneHundredFifteenDI_9642827, prime_oneHundredFifteenDI_134499857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584011 : Nat.totient 135960691671824579163806584011 = 77289275502562010953222393344 := by
  rw [← show ((([(3, 1), (7, 1), (193, 1), (33545692492431428365113887, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_193, prime_oneHundredFifteenDI_33545692492431428365113887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584012 : Nat.totient 135960691671824579163806584012 = 67980211907978792377885676976 := by
  rw [← show ((([(2, 2), (507589, 1), (66963966748602008299927, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_507589, prime_oneHundredFifteenDI_66963966748602008299927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584013 : Nat.totient 135960691671824579163806584013 = 132992083370739218068934400000 := by
  rw [← show ((([(53, 1), (491, 1), (1061, 1), (23021, 1), (346441, 1), (617429181011, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_53, prime_oneHundredFifteenDI_491, prime_oneHundredFifteenDI_1061, prime_oneHundredFifteenDI_23021, prime_oneHundredFifteenDI_346441, prime_oneHundredFifteenDI_617429181011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584014 : Nat.totient 135960691671824579163806584014 = 45318807496058504181979775256 := by
  rw [← show ((([(2, 1), (3, 3), (31847, 1), (79058956464196627139603, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_31847, prime_oneHundredFifteenDI_79058956464196627139603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584015 : Nat.totient 135960691671824579163806584015 = 108768553337459663331045267208 := by
  rw [← show ((([(5, 1), (27192138334364915832761316803, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_27192138334364915832761316803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584016 : Nat.totient 135960691671824579163806584016 = 67980345835912289581903292000 := by
  rw [← show ((([(2, 4), (8497543229489036197737911501, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_8497543229489036197737911501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584017 : Nat.totient 135960691671824579163806584017 = 90640461114549719442537722676 := by
  rw [← show ((([(3, 1), (45320230557274859721268861339, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_45320230557274859721268861339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584018 : Nat.totient 135960691671824579163806584018 = 53786646695269960218712828800 := by
  rw [← show ((([(2, 1), (7, 2), (13, 1), (120976789, 1), (865679951, 1), (1019024263, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_13, prime_oneHundredFifteenDI_120976789, prime_oneHundredFifteenDI_865679951, prime_oneHundredFifteenDI_1019024263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584019 : Nat.totient 135960691671824579163806584019 = 123596750035989136404721944000 := by
  rw [← show ((([(11, 1), (32089, 1), (4586191, 1), (83987056188276271, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_32089, prime_oneHundredFifteenDI_4586191, prime_oneHundredFifteenDI_83987056188276271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584020 : Nat.totient 135960691671824579163806584020 = 35641672845043279509608052736 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (59, 1), (38406975048538016712939713, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_59, prime_oneHundredFifteenDI_38406975048538016712939713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584021 : Nat.totient 135960691671824579163806584021 = 135954426486286880659956224400 := by
  rw [← show ((([(21701, 1), (29601798143, 1), (211648661139247, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_21701, prime_oneHundredFifteenDI_29601798143, prime_oneHundredFifteenDI_211648661139247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584022 : Nat.totient 135960691671824579163806584022 = 67161067472954887715343068928 := by
  rw [← show ((([(2, 1), (83, 1), (282589, 1), (173355797, 1), (16719052275049, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_83, prime_oneHundredFifteenDI_282589, prime_oneHundredFifteenDI_173355797, prime_oneHundredFifteenDI_16719052275049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584023 : Nat.totient 135960691671824579163806584023 = 86699428718075020686173467968 := by
  rw [← show ((([(3, 2), (23, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_23, prime_oneHundredFifteenDI_607213, prime_oneHundredFifteenDI_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584024 : Nat.totient 135960691671824579163806584024 = 67716704903119173492486972160 := by
  rw [← show ((([(2, 3), (281, 1), (3119, 1), (19391065960070321374877, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_281, prime_oneHundredFifteenDI_3119, prime_oneHundredFifteenDI_19391065960070321374877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584025 : Nat.totient 135960691671824579163806584025 = 93170692602677636672303698560 := by
  rw [← show ((([(5, 2), (7, 1), (1567, 1), (495799769064908666838569, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_1567, prime_oneHundredFifteenDI_495799769064908666838569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584026 : Nat.totient 135960691671824579163806584026 = 41472914978308109858052341760 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (37, 1), (2281, 1), (3989, 1), (6980443, 1), (567203840477, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_17, prime_oneHundredFifteenDI_37, prime_oneHundredFifteenDI_2281, prime_oneHundredFifteenDI_3989, prime_oneHundredFifteenDI_6980443, prime_oneHundredFifteenDI_567203840477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584027 : Nat.totient 135960691671824579163806584027 = 128739644595606690464827852800 := by
  rw [← show ((([(19, 1), (1987, 1), (578401, 1), (736363, 1), (8455531342393, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_19, prime_oneHundredFifteenDI_1987, prime_oneHundredFifteenDI_578401, prime_oneHundredFifteenDI_736363, prime_oneHundredFifteenDI_8455531342393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584028 : Nat.totient 135960691671824579163806584028 = 67979753109841055463362096880 := by
  rw [← show ((([(2, 2), (114691, 1), (296363035617059270482877, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_114691, prime_oneHundredFifteenDI_296363035617059270482877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584029 : Nat.totient 135960691671824579163806584029 = 88796944874750980209529651200 := by
  rw [← show ((([(3, 1), (73, 1), (151, 1), (9043, 1), (183643819, 1), (2475731011073, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_73, prime_oneHundredFifteenDI_151, prime_oneHundredFifteenDI_9043, prime_oneHundredFifteenDI_183643819, prime_oneHundredFifteenDI_2475731011073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584030 : Nat.totient 135960691671824579163806584030 = 49256269437056481194053302400 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (269, 1), (260171, 1), (17660765089967180327, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_269, prime_oneHundredFifteenDI_260171, prime_oneHundredFifteenDI_17660765089967180327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584031 : Nat.totient 135960691671824579163806584031 = 125502176927838073074283000632 := by
  rw [← show ((([(13, 1), (10458514743986506089523583387, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_13, prime_oneHundredFifteenDI_10458514743986506089523583387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584032 : Nat.totient 135960691671824579163806584032 = 38845609797494654448095757312 := by
  rw [← show ((([(2, 5), (3, 2), (7, 1), (133963, 1), (3201437, 1), (157250854089767, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_133963, prime_oneHundredFifteenDI_3201437, prime_oneHundredFifteenDI_157250854089767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584033 : Nat.totient 135960691671824579163806584033 = 135960682142751439986935821588 := by
  rw [← show ((([(14267987, 1), (9529073139176856494459, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_14267987, prime_oneHundredFifteenDI_9529073139176856494459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584034 : Nat.totient 135960691671824579163806584034 = 67980345810774888269796634480 := by
  rw [← show ((([(2, 1), (2704350581, 1), (25137401309402306957, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_2704350581, prime_oneHundredFifteenDI_25137401309402306957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584035 : Nat.totient 135960691671824579163806584035 = 70781521647032325221437255680 := by
  rw [← show ((([(3, 1), (5, 1), (43, 1), (1597, 1), (432499, 1), (305185311208195361, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_43, prime_oneHundredFifteenDI_1597, prime_oneHundredFifteenDI_432499, prime_oneHundredFifteenDI_305185311208195361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584036 : Nat.totient 135960691671824579163806584036 = 67963921494550538066930384064 := by
  rw [← show ((([(2, 2), (4139, 1), (92012407939, 1), (89250683631929, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_4139, prime_oneHundredFifteenDI_92012407939, prime_oneHundredFifteenDI_89250683631929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584037 : Nat.totient 135960691671824579163806584037 = 135903398876595571067396161920 := by
  rw [← show ((([(2377, 1), (1450877, 1), (198474611, 1), (198631731323, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2377, prime_oneHundredFifteenDI_1450877, prime_oneHundredFifteenDI_198474611, prime_oneHundredFifteenDI_198631731323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584038 : Nat.totient 135960691671824579163806584038 = 42093541490037688847755238400 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (31, 1), (271, 1), (439, 1), (1436537, 1), (147486339107659, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_29, prime_oneHundredFifteenDI_31, prime_oneHundredFifteenDI_271, prime_oneHundredFifteenDI_439, prime_oneHundredFifteenDI_1436537, prime_oneHundredFifteenDI_147486339107659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584039 : Nat.totient 135960691671824579163806584039 = 113624200804780966077758356992 := by
  rw [← show ((([(7, 1), (67, 1), (113, 1), (719, 1), (3568068543723551863573, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_67, prime_oneHundredFifteenDI_113, prime_oneHundredFifteenDI_719, prime_oneHundredFifteenDI_3568068543723551863573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584040 : Nat.totient 135960691671824579163806584040 = 53956054017768822405884713728 := by
  rw [← show ((([(2, 3), (5, 1), (127, 1), (2577668428667, 1), (10382993943589, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_127, prime_oneHundredFifteenDI_2577668428667, prime_oneHundredFifteenDI_10382993943589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584041 : Nat.totient 135960691671824579163806584041 = 80473034728785468481645127040 := by
  rw [← show ((([(3, 5), (11, 1), (47, 1), (463, 1), (2337413551456172853497, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_47, prime_oneHundredFifteenDI_463, prime_oneHundredFifteenDI_2337413551456172853497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584042 : Nat.totient 135960691671824579163806584042 = 67433832983865417208847769600 := by
  rw [← show ((([(2, 1), (163, 1), (881, 1), (1279, 1), (63022361, 1), (5872927549553, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_163, prime_oneHundredFifteenDI_881, prime_oneHundredFifteenDI_1279, prime_oneHundredFifteenDI_63022361, prime_oneHundredFifteenDI_5872927549553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584043 : Nat.totient 135960691671824579163806584043 = 125839890083605324216364236800 := by
  rw [← show ((([(17, 1), (61, 1), (5023, 1), (416833, 1), (62619462674672521, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_17, prime_oneHundredFifteenDI_61, prime_oneHundredFifteenDI_5023, prime_oneHundredFifteenDI_416833, prime_oneHundredFifteenDI_62619462674672521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584044 : Nat.totient 135960691671824579163806584044 = 41833210946596930481897203200 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (49331, 1), (28051407961, 1), (629816716439, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_13, prime_oneHundredFifteenDI_49331, prime_oneHundredFifteenDI_28051407961, prime_oneHundredFifteenDI_629816716439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584045 : Nat.totient 135960691671824579163806584045 = 108667982485495050720240762624 := by
  rw [← show ((([(5, 1), (1093, 1), (102983, 1), (58233839, 1), (4148415406349, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_1093, prime_oneHundredFifteenDI_102983, prime_oneHundredFifteenDI_58233839, prime_oneHundredFifteenDI_4148415406349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584046 : Nat.totient 135960691671824579163806584046 = 51384378829622747480547655680 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (23, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_19, prime_oneHundredFifteenDI_23, prime_oneHundredFifteenDI_41, prime_oneHundredFifteenDI_397, prime_oneHundredFifteenDI_13617913, prime_oneHundredFifteenDI_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584047 : Nat.totient 135960691671824579163806584047 = 90630476026679163684650112000 := by
  rw [← show ((([(3, 1), (13093, 1), (29641, 1), (19870973, 1), (5876800637101, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_13093, prime_oneHundredFifteenDI_29641, prime_oneHundredFifteenDI_19870973, prime_oneHundredFifteenDI_5876800637101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584048 : Nat.totient 135960691671824579163806584048 = 67202192588088597584100139008 := by
  rw [← show ((([(2, 4), (97, 1), (1693, 1), (1789, 1), (28923733390850689687, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_97, prime_oneHundredFifteenDI_1693, prime_oneHundredFifteenDI_1789, prime_oneHundredFifteenDI_28923733390850689687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584049 : Nat.totient 135960691671824579163806584049 = 135575533905048872140679652864 := by
  rw [← show ((([(353, 1), (385157766775707023126930833, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_353, prime_oneHundredFifteenDI_385157766775707023126930833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584050 : Nat.totient 135960691671824579163806584050 = 36228036054326961414314787840 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (1289, 1), (1723669, 1), (135985957393556749, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_1289, prime_oneHundredFifteenDI_1723669, prime_oneHundredFifteenDI_135985957393556749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584051 : Nat.totient 135960691671824579163806584051 = 135960691671824579163806584050 := by
  rw [← show ((([(135960691671824579163806584051, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_135960691671824579163806584051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584052 : Nat.totient 135960691671824579163806584052 = 61800314280167665971276555200 := by
  rw [← show ((([(2, 2), (11, 1), (532228031, 1), (5805811681899548393, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_532228031, prime_oneHundredFifteenDI_5805811681899548393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584053 : Nat.totient 135960691671824579163806584053 = 77691823812285758669411696880 := by
  rw [← show ((([(3, 1), (7, 1), (418994616571, 1), (15452033021388883, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_418994616571, prime_oneHundredFifteenDI_15452033021388883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584054 : Nat.totient 135960691671824579163806584054 = 67742158195974048244036992000 := by
  rw [← show ((([(2, 1), (311, 1), (3457, 1), (63230061040149014564701, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_311, prime_oneHundredFifteenDI_3457, prime_oneHundredFifteenDI_63230061040149014564701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584055 : Nat.totient 135960691671824579163806584055 = 108768553337456306783009434368 := by
  rw [← show ((([(5, 1), (33763383185377, 1), (805373625772843, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_33763383185377, prime_oneHundredFifteenDI_805373625772843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584056 : Nat.totient 135960691671824579163806584056 = 45177533438747490665360087040 := by
  rw [← show ((([(2, 3), (3, 1), (331, 1), (7823, 1), (19713929, 1), (110975628033097, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_331, prime_oneHundredFifteenDI_7823, prime_oneHundredFifteenDI_19713929, prime_oneHundredFifteenDI_110975628033097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584057 : Nat.totient 135960691671824579163806584057 = 125502176922568524207176843088 := by
  rw [← show ((([(13, 1), (23816494903, 1), (439129048442351563, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_13, prime_oneHundredFifteenDI_23816494903, prime_oneHundredFifteenDI_439129048442351563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584058 : Nat.totient 135960691671824579163806584058 = 67838282686015440935544000000 := by
  rw [← show ((([(2, 1), (479, 1), (478651, 1), (2190099601, 1), (135383276201, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_479, prime_oneHundredFifteenDI_478651, prime_oneHundredFifteenDI_2190099601, prime_oneHundredFifteenDI_135383276201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584059 : Nat.totient 135960691671824579163806584059 = 90331108004943747703825988112 := by
  rw [← show ((([(3, 2), (293, 1), (51558851600995289785288807, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_293, prime_oneHundredFifteenDI_51558851600995289785288807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584060 : Nat.totient 135960691671824579163806584060 = 43856517674530438254895595520 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (17, 1), (2657, 1), (21500316536914473447941, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_17, prime_oneHundredFifteenDI_2657, prime_oneHundredFifteenDI_21500316536914473447941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584061 : Nat.totient 135960691671824579163806584061 = 134614546209727306102778796000 := by
  rw [← show ((([(101, 1), (1346145462097273061027787961, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_101, prime_oneHundredFifteenDI_1346145462097273061027787961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584062 : Nat.totient 135960691671824579163806584062 = 45320225971691327071163486400 := by
  rw [← show ((([(2, 1), (3, 1), (10537463, 1), (159178729, 1), (13509554247451, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_10537463, prime_oneHundredFifteenDI_159178729, prime_oneHundredFifteenDI_13509554247451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584063 : Nat.totient 135960691671824579163806584063 = 120260070973875392443340301600 := by
  rw [← show ((([(11, 1), (37, 1), (423811879, 1), (788217060554422271, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_37, prime_oneHundredFifteenDI_423811879, prime_oneHundredFifteenDI_788217060554422271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584064 : Nat.totient 135960691671824579163806584064 = 67980345835912289581903291904 := by
  rw [← show ((([(2, 8), (531096451843064762358619469, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_531096451843064762358619469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584065 : Nat.totient 135960691671824579163806584065 = 68622578443914038952240328704 := by
  rw [← show ((([(3, 1), (5, 1), (19, 1), (937, 1), (1948313, 1), (261318517715367989, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_19, prime_oneHundredFifteenDI_937, prime_oneHundredFifteenDI_1948313, prime_oneHundredFifteenDI_261318517715367989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584066 : Nat.totient 135960691671824579163806584066 = 65853423144371862882570367680 := by
  rw [← show ((([(2, 1), (53, 1), (79, 1), (55430399069, 1), (292908789113711, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_53, prime_oneHundredFifteenDI_79, prime_oneHundredFifteenDI_55430399069, prime_oneHundredFifteenDI_292908789113711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584067 : Nat.totient 135960691671824579163806584067 = 112506873038395999977989318976 := by
  rw [← show ((([(7, 2), (29, 1), (9133, 1), (10476249422528165885419, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_29, prime_oneHundredFifteenDI_9133, prime_oneHundredFifteenDI_10476249422528165885419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584068 : Nat.totient 135960691671824579163806584068 = 45320214138055627840994345472 := by
  rw [← show ((([(2, 2), (3, 3), (2792473, 1), (238816003, 1), (1887718368409, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_2792473, prime_oneHundredFifteenDI_238816003, prime_oneHundredFifteenDI_1887718368409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584069 : Nat.totient 135960691671824579163806584069 = 125854181725685718907184647680 := by
  rw [← show ((([(23, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_23, prime_oneHundredFifteenDI_31, prime_oneHundredFifteenDI_3599009, prime_oneHundredFifteenDI_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584070 : Nat.totient 135960691671824579163806584070 = 49636815557740527051985471488 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (89, 1), (102211363, 1), (114969019264351177, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_13, prime_oneHundredFifteenDI_89, prime_oneHundredFifteenDI_102211363, prime_oneHundredFifteenDI_114969019264351177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584071 : Nat.totient 135960691671824579163806584071 = 89793353931829497505043647104 := by
  rw [← show ((([(3, 1), (107, 1), (1291988273, 1), (327830805790948087, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_107, prime_oneHundredFifteenDI_1291988273, prime_oneHundredFifteenDI_327830805790948087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584072 : Nat.totient 135960691671824579163806584072 = 67967265145930393817119376064 := by
  rw [← show ((([(2, 3), (5197, 1), (3270172495473941195973797, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5197, prime_oneHundredFifteenDI_3270172495473941195973797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584073 : Nat.totient 135960691671824579163806584073 = 135854260465277706029956713600 := by
  rw [← show ((([(1367, 1), (38603, 1), (39371, 1), (79224553, 1), (826014271, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_1367, prime_oneHundredFifteenDI_38603, prime_oneHundredFifteenDI_39371, prime_oneHundredFifteenDI_79224553, prime_oneHundredFifteenDI_826014271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584074 : Nat.totient 135960691671824579163806584074 = 35314465369305085497092619120 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (11, 1), (294287211410875712475771827, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_294287211410875712475771827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584075 : Nat.totient 135960691671824579163806584075 = 108768553337445158633588120960 := by
  rw [← show ((([(5, 2), (7578033636209, 1), (717656839221107, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_7578033636209, prime_oneHundredFifteenDI_717656839221107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584076 : Nat.totient 135960691671824579163806584076 = 67980345262929164237320201440 := by
  rw [← show ((([(2, 2), (118642841, 1), (286491562672172902459, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_118642841, prime_oneHundredFifteenDI_286491562672172902459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584077 : Nat.totient 135960691671824579163806584077 = 85308669284282088887094327168 := by
  rw [← show ((([(3, 2), (17, 1), (888631971711271759240565909, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_17, prime_oneHundredFifteenDI_888631971711271759240565909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584078 : Nat.totient 135960691671824579163806584078 = 65464204636510036714828235520 := by
  rw [← show ((([(2, 1), (43, 1), (71, 1), (86288292067, 1), (258050492573089, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_43, prime_oneHundredFifteenDI_71, prime_oneHundredFifteenDI_86288292067, prime_oneHundredFifteenDI_258050492573089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584079 : Nat.totient 135960691671824579163806584079 = 132752120605373994705755712000 := by
  rw [← show ((([(59, 1), (173, 1), (1051, 1), (25841, 1), (490459576096940467, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_59, prime_oneHundredFifteenDI_173, prime_oneHundredFifteenDI_1051, prime_oneHundredFifteenDI_25841, prime_oneHundredFifteenDI_490459576096940467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584080 : Nat.totient 135960691671824579163806584080 = 36256184220204781571698183680 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (160699277, 1), (3525236034297377371, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_160699277, prime_oneHundredFifteenDI_3525236034297377371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584081 : Nat.totient 135960691671824579163806584081 = 116537735718706782140405643492 := by
  rw [← show ((([(7, 1), (19422955953117797023400940583, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_19422955953117797023400940583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584082 : Nat.totient 135960691671824579163806584082 = 67733788236911957147838710400 := by
  rw [← show ((([(2, 1), (317, 1), (2111, 1), (9363721, 1), (10848942541098283, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_317, prime_oneHundredFifteenDI_2111, prime_oneHundredFifteenDI_9363721, prime_oneHundredFifteenDI_10848942541098283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584083 : Nat.totient 135960691671824579163806584083 = 83668088752263952963458310944 := by
  rw [← show ((([(3, 1), (13, 1), (2865383, 1), (1216651170656360899459, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_13, prime_oneHundredFifteenDI_2865383, prime_oneHundredFifteenDI_1216651170656360899459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584084 : Nat.totient 135960691671824579163806584084 = 64196660004325863199047023616 := by
  rw [← show ((([(2, 2), (19, 1), (313, 1), (4548559, 1), (337083613, 1), (3727725829, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_19, prime_oneHundredFifteenDI_313, prime_oneHundredFifteenDI_4548559, prime_oneHundredFifteenDI_337083613, prime_oneHundredFifteenDI_3727725829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584085 : Nat.totient 135960691671824579163806584085 = 98522326037119275950245171200 := by
  rw [← show ((([(5, 1), (11, 1), (277, 1), (82013, 1), (15501091, 1), (7019819453617, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_277, prime_oneHundredFifteenDI_82013, prime_oneHundredFifteenDI_15501091, prime_oneHundredFifteenDI_7019819453617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584086 : Nat.totient 135960691671824579163806584086 = 45231192776219309898633752496 := by
  rw [← show ((([(2, 1), (3, 2), (509, 1), (14839630175924970439184303, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_509, prime_oneHundredFifteenDI_14839630175924970439184303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584087 : Nat.totient 135960691671824579163806584087 = 132644577240601154823960733440 := by
  rw [← show ((([(41, 1), (652500499153, 1), (5082163822594319, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_41, prime_oneHundredFifteenDI_652500499153, prime_oneHundredFifteenDI_5082163822594319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584088 : Nat.totient 135960691671824579163806584088 = 56953769040076267681984980864 := by
  rw [← show ((([(2, 3), (7, 1), (47, 1), (757, 1), (68238834541154181621887, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_47, prime_oneHundredFifteenDI_757, prime_oneHundredFifteenDI_68238834541154181621887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584089 : Nat.totient 135960691671824579163806584089 = 90640318882342205606633916080 := by
  rw [← show ((([(3, 1), (637271, 1), (71116103756917951266053, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_637271, prime_oneHundredFifteenDI_71116103756917951266053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584090 : Nat.totient 135960691671824579163806584090 = 54384276668729831665522633632 := by
  rw [← show ((([(2, 1), (5, 1), (13596069167182457916380658409, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_13596069167182457916380658409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584091 : Nat.totient 135960691671824579163806584091 = 135934100556155336420909064000 := by
  rw [← show ((([(5119, 1), (4370089, 1), (6077681734656833501, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_5119, prime_oneHundredFifteenDI_4370089, prime_oneHundredFifteenDI_6077681734656833501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584092 : Nat.totient 135960691671824579163806584092 = 43341182614965141864089637120 := by
  rw [← show ((([(2, 2), (3, 1), (23, 1), (5879, 1), (35267, 1), (88812211, 1), (26752207429, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_23, prime_oneHundredFifteenDI_5879, prime_oneHundredFifteenDI_35267, prime_oneHundredFifteenDI_88812211, prime_oneHundredFifteenDI_26752207429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584093 : Nat.totient 135960691671824579163806584093 = 135200950991055043114100899392 := by
  rw [← show ((([(179, 1), (769309, 1), (16899167, 1), (58424394937189, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_179, prime_oneHundredFifteenDI_769309, prime_oneHundredFifteenDI_16899167, prime_oneHundredFifteenDI_58424394937189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584094 : Nat.totient 135960691671824579163806584094 = 63959385640319817590675865600 := by
  rw [← show ((([(2, 1), (17, 1), (2917, 1), (351361, 1), (230798803, 1), (16904834081, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_17, prime_oneHundredFifteenDI_2917, prime_oneHundredFifteenDI_351361, prime_oneHundredFifteenDI_230798803, prime_oneHundredFifteenDI_16904834081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584095 : Nat.totient 135960691671824579163806584095 = 62151295606929720541576396800 := by
  rw [← show ((([(3, 3), (5, 1), (7, 1), (28729, 1), (20037609601, 1), (249928128199, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_7, prime_oneHundredFifteenDI_28729, prime_oneHundredFifteenDI_20037609601, prime_oneHundredFifteenDI_249928128199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584096 : Nat.totient 135960691671824579163806584096 = 55079322847371510109714575360 := by
  rw [← show ((([(2, 5), (11, 1), (13, 1), (29, 1), (22480327, 1), (45575005254974837, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_11, prime_oneHundredFifteenDI_13, prime_oneHundredFifteenDI_29, prime_oneHundredFifteenDI_22480327, prime_oneHundredFifteenDI_45575005254974837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584097 : Nat.totient 135960691671824579163806584097 = 135960691671824579163806584096 := by
  rw [← show ((([(135960691671824579163806584097, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_135960691671824579163806584097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584098 : Nat.totient 135960691671824579163806584098 = 45320230557272654676057100320 := by
  rw [← show ((([(2, 1), (3, 1), (20951102358793, 1), (1081571503521731, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_20951102358793, prime_oneHundredFifteenDI_1081571503521731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584099 : Nat.totient 135960691671824579163806584099 = 134968262395710197835714468480 := by
  rw [← show ((([(137, 1), (8725481, 1), (113737432678328802067, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_137, prime_oneHundredFifteenDI_8725481, prime_oneHundredFifteenDI_113737432678328802067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584100 : Nat.totient 135960691671824579163806584100 = 51129997473385135084386816000 := by
  rw [← show ((([(2, 2), (5, 2), (31, 1), (37, 1), (661, 1), (1088447, 1), (1647559854904009, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_2, prime_oneHundredFifteenDI_5, prime_oneHundredFifteenDI_31, prime_oneHundredFifteenDI_37, prime_oneHundredFifteenDI_661, prime_oneHundredFifteenDI_1088447, prime_oneHundredFifteenDI_1647559854904009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFifteenDI_135960691671824579163806584101 : Nat.totient 135960691671824579163806584101 = 90629875985376001152283993392 := by
  rw [← show ((([(3, 1), (8563, 1), (5292564586859145126856109, 1)] : List FactorBlock).map factorBlockValue).prod) = 135960691671824579163806584101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFifteenDI_3, prime_oneHundredFifteenDI_8563, prime_oneHundredFifteenDI_5292564586859145126856109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFifteenDI : certifiedKill 1 135960691671824579163806583999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFifteenDI_135960691671824579163806584000, phi_oneHundredFifteenDI_135960691671824579163806584001, phi_oneHundredFifteenDI_135960691671824579163806584002,
    phi_oneHundredFifteenDI_135960691671824579163806584003, phi_oneHundredFifteenDI_135960691671824579163806584004, phi_oneHundredFifteenDI_135960691671824579163806584005,
    phi_oneHundredFifteenDI_135960691671824579163806584006, phi_oneHundredFifteenDI_135960691671824579163806584007, phi_oneHundredFifteenDI_135960691671824579163806584008,
    phi_oneHundredFifteenDI_135960691671824579163806584009, phi_oneHundredFifteenDI_135960691671824579163806584010, phi_oneHundredFifteenDI_135960691671824579163806584011,
    phi_oneHundredFifteenDI_135960691671824579163806584012, phi_oneHundredFifteenDI_135960691671824579163806584013, phi_oneHundredFifteenDI_135960691671824579163806584014,
    phi_oneHundredFifteenDI_135960691671824579163806584015, phi_oneHundredFifteenDI_135960691671824579163806584016, phi_oneHundredFifteenDI_135960691671824579163806584017,
    phi_oneHundredFifteenDI_135960691671824579163806584018, phi_oneHundredFifteenDI_135960691671824579163806584019, phi_oneHundredFifteenDI_135960691671824579163806584020,
    phi_oneHundredFifteenDI_135960691671824579163806584021, phi_oneHundredFifteenDI_135960691671824579163806584022, phi_oneHundredFifteenDI_135960691671824579163806584023,
    phi_oneHundredFifteenDI_135960691671824579163806584024, phi_oneHundredFifteenDI_135960691671824579163806584025, phi_oneHundredFifteenDI_135960691671824579163806584026,
    phi_oneHundredFifteenDI_135960691671824579163806584027, phi_oneHundredFifteenDI_135960691671824579163806584028, phi_oneHundredFifteenDI_135960691671824579163806584029,
    phi_oneHundredFifteenDI_135960691671824579163806584030, phi_oneHundredFifteenDI_135960691671824579163806584031, phi_oneHundredFifteenDI_135960691671824579163806584032,
    phi_oneHundredFifteenDI_135960691671824579163806584033, phi_oneHundredFifteenDI_135960691671824579163806584034, phi_oneHundredFifteenDI_135960691671824579163806584035,
    phi_oneHundredFifteenDI_135960691671824579163806584036, phi_oneHundredFifteenDI_135960691671824579163806584037, phi_oneHundredFifteenDI_135960691671824579163806584038,
    phi_oneHundredFifteenDI_135960691671824579163806584039, phi_oneHundredFifteenDI_135960691671824579163806584040, phi_oneHundredFifteenDI_135960691671824579163806584041,
    phi_oneHundredFifteenDI_135960691671824579163806584042, phi_oneHundredFifteenDI_135960691671824579163806584043, phi_oneHundredFifteenDI_135960691671824579163806584044,
    phi_oneHundredFifteenDI_135960691671824579163806584045, phi_oneHundredFifteenDI_135960691671824579163806584046, phi_oneHundredFifteenDI_135960691671824579163806584047,
    phi_oneHundredFifteenDI_135960691671824579163806584048, phi_oneHundredFifteenDI_135960691671824579163806584049, phi_oneHundredFifteenDI_135960691671824579163806584050,
    phi_oneHundredFifteenDI_135960691671824579163806584051, phi_oneHundredFifteenDI_135960691671824579163806584052, phi_oneHundredFifteenDI_135960691671824579163806584053,
    phi_oneHundredFifteenDI_135960691671824579163806584054, phi_oneHundredFifteenDI_135960691671824579163806584055, phi_oneHundredFifteenDI_135960691671824579163806584056,
    phi_oneHundredFifteenDI_135960691671824579163806584057, phi_oneHundredFifteenDI_135960691671824579163806584058, phi_oneHundredFifteenDI_135960691671824579163806584059,
    phi_oneHundredFifteenDI_135960691671824579163806584060, phi_oneHundredFifteenDI_135960691671824579163806584061, phi_oneHundredFifteenDI_135960691671824579163806584062,
    phi_oneHundredFifteenDI_135960691671824579163806584063, phi_oneHundredFifteenDI_135960691671824579163806584064, phi_oneHundredFifteenDI_135960691671824579163806584065,
    phi_oneHundredFifteenDI_135960691671824579163806584066, phi_oneHundredFifteenDI_135960691671824579163806584067, phi_oneHundredFifteenDI_135960691671824579163806584068,
    phi_oneHundredFifteenDI_135960691671824579163806584069, phi_oneHundredFifteenDI_135960691671824579163806584070, phi_oneHundredFifteenDI_135960691671824579163806584071,
    phi_oneHundredFifteenDI_135960691671824579163806584072, phi_oneHundredFifteenDI_135960691671824579163806584073, phi_oneHundredFifteenDI_135960691671824579163806584074,
    phi_oneHundredFifteenDI_135960691671824579163806584075, phi_oneHundredFifteenDI_135960691671824579163806584076, phi_oneHundredFifteenDI_135960691671824579163806584077,
    phi_oneHundredFifteenDI_135960691671824579163806584078, phi_oneHundredFifteenDI_135960691671824579163806584079, phi_oneHundredFifteenDI_135960691671824579163806584080,
    phi_oneHundredFifteenDI_135960691671824579163806584081, phi_oneHundredFifteenDI_135960691671824579163806584082, phi_oneHundredFifteenDI_135960691671824579163806584083,
    phi_oneHundredFifteenDI_135960691671824579163806584084, phi_oneHundredFifteenDI_135960691671824579163806584085, phi_oneHundredFifteenDI_135960691671824579163806584086,
    phi_oneHundredFifteenDI_135960691671824579163806584087, phi_oneHundredFifteenDI_135960691671824579163806584088, phi_oneHundredFifteenDI_135960691671824579163806584089,
    phi_oneHundredFifteenDI_135960691671824579163806584090, phi_oneHundredFifteenDI_135960691671824579163806584091, phi_oneHundredFifteenDI_135960691671824579163806584092,
    phi_oneHundredFifteenDI_135960691671824579163806584093, phi_oneHundredFifteenDI_135960691671824579163806584094, phi_oneHundredFifteenDI_135960691671824579163806584095,
    phi_oneHundredFifteenDI_135960691671824579163806584096, phi_oneHundredFifteenDI_135960691671824579163806584097, phi_oneHundredFifteenDI_135960691671824579163806584098,
    phi_oneHundredFifteenDI_135960691671824579163806584099, phi_oneHundredFifteenDI_135960691671824579163806584100, phi_oneHundredFifteenDI_135960691671824579163806584101
    ]

end TotientTailPeriodKiller
end Erdos249257
