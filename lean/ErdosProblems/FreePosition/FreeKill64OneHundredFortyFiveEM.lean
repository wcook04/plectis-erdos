import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFortyFiveEMFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortyFiveEMFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortyFiveEMFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortyFiveEMFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortyFiveEMFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortyFiveEMFastPow a n * oneHundredFortyFiveEMFastPow a n * a else oneHundredFortyFiveEMFastPow a n * oneHundredFortyFiveEMFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortyFiveEM_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFortyFiveEM_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFortyFiveEM_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFortyFiveEM_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFortyFiveEM_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFortyFiveEM_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFortyFiveEM_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFortyFiveEM_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFortyFiveEM_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFortyFiveEM_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFortyFiveEM_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFortyFiveEM_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFortyFiveEM_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFortyFiveEM_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFortyFiveEM_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFortyFiveEM_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFortyFiveEM_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFortyFiveEM_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFortyFiveEM_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFortyFiveEM_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFortyFiveEM_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFortyFiveEM_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFortyFiveEM_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFortyFiveEM_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFortyFiveEM_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFortyFiveEM_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFortyFiveEM_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFortyFiveEM_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFortyFiveEM_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFortyFiveEM_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFortyFiveEM_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFortyFiveEM_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFortyFiveEM_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFortyFiveEM_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFortyFiveEM_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFortyFiveEM_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFortyFiveEM_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFortyFiveEM_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFortyFiveEM_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFortyFiveEM_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFortyFiveEM_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFortyFiveEM_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFortyFiveEM_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFortyFiveEM_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFortyFiveEM_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFortyFiveEM_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFortyFiveEM_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFortyFiveEM_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFortyFiveEM_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFortyFiveEM_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFortyFiveEM_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFortyFiveEM_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFortyFiveEM_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFortyFiveEM_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFortyFiveEM_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFortyFiveEM_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFortyFiveEM_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFortyFiveEM_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFortyFiveEM_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFortyFiveEM_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFortyFiveEM_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFortyFiveEM_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredFortyFiveEM_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFortyFiveEM_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFortyFiveEM_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFortyFiveEM_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFortyFiveEM_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFortyFiveEM_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredFortyFiveEM_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFortyFiveEM_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFortyFiveEM_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFortyFiveEM_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFortyFiveEM_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFortyFiveEM_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredFortyFiveEM_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFortyFiveEM_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFortyFiveEM_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredFortyFiveEM_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFortyFiveEM_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredFortyFiveEM_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFortyFiveEM_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredFortyFiveEM_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredFortyFiveEM_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredFortyFiveEM_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFortyFiveEM_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFortyFiveEM_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredFortyFiveEM_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFortyFiveEM_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredFortyFiveEM_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredFortyFiveEM_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFortyFiveEM_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFortyFiveEM_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredFortyFiveEM_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredFortyFiveEM_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredFortyFiveEM_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFortyFiveEM_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredFortyFiveEM_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredFortyFiveEM_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredFortyFiveEM_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredFortyFiveEM_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredFortyFiveEM_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredFortyFiveEM_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredFortyFiveEM_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredFortyFiveEM_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredFortyFiveEM_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredFortyFiveEM_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredFortyFiveEM_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2707 : Nat.Prime 2707 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2969 : Nat.Prime 2969 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3467 : Nat.Prime 3467 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3539 : Nat.Prime 3539 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3769 : Nat.Prime 3769 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3851 : Nat.Prime 3851 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4051 : Nat.Prime 4051 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4159 : Nat.Prime 4159 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4561 : Nat.Prime 4561 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4591 : Nat.Prime 4591 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4597 : Nat.Prime 4597 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4817 : Nat.Prime 4817 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4903 : Nat.Prime 4903 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5281 : Nat.Prime 5281 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5303 : Nat.Prime 5303 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5323 : Nat.Prime 5323 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5479 : Nat.Prime 5479 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5741 : Nat.Prime 5741 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5783 : Nat.Prime 5783 := by norm_num

private theorem prime_oneHundredFortyFiveEM_6067 : Nat.Prime 6067 := by norm_num

private theorem prime_oneHundredFortyFiveEM_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_oneHundredFortyFiveEM_6607 : Nat.Prime 6607 := by norm_num

private theorem prime_oneHundredFortyFiveEM_6653 : Nat.Prime 6653 := by norm_num

private theorem prime_oneHundredFortyFiveEM_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7297 : Nat.Prime 7297 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7649 : Nat.Prime 7649 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7687 : Nat.Prime 7687 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7933 : Nat.Prime 7933 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7963 : Nat.Prime 7963 := by norm_num

private theorem prime_oneHundredFortyFiveEM_8179 : Nat.Prime 8179 := by norm_num

private theorem prime_oneHundredFortyFiveEM_8231 : Nat.Prime 8231 := by norm_num

private theorem prime_oneHundredFortyFiveEM_8461 : Nat.Prime 8461 := by norm_num

private theorem prime_oneHundredFortyFiveEM_8609 : Nat.Prime 8609 := by norm_num

private theorem prime_oneHundredFortyFiveEM_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_oneHundredFortyFiveEM_9049 : Nat.Prime 9049 := by norm_num

private theorem prime_oneHundredFortyFiveEM_9439 : Nat.Prime 9439 := by norm_num

private theorem prime_oneHundredFortyFiveEM_9539 : Nat.Prime 9539 := by norm_num

private theorem prime_oneHundredFortyFiveEM_9887 : Nat.Prime 9887 := by norm_num

private theorem prime_oneHundredFortyFiveEM_9907 : Nat.Prime 9907 := by norm_num

private theorem prime_oneHundredFortyFiveEM_9923 : Nat.Prime 9923 := by norm_num

private theorem prime_oneHundredFortyFiveEM_10169 : Nat.Prime 10169 := by norm_num

private theorem prime_oneHundredFortyFiveEM_10321 : Nat.Prime 10321 := by norm_num

private theorem prime_oneHundredFortyFiveEM_10529 : Nat.Prime 10529 := by norm_num

private theorem prime_oneHundredFortyFiveEM_10939 : Nat.Prime 10939 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11393 : Nat.Prime 11393 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11681 : Nat.Prime 11681 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11807 : Nat.Prime 11807 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11909 : Nat.Prime 11909 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12251 : Nat.Prime 12251 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12377 : Nat.Prime 12377 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12577 : Nat.Prime 12577 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12899 : Nat.Prime 12899 := by norm_num

private theorem prime_oneHundredFortyFiveEM_13063 : Nat.Prime 13063 := by norm_num

private theorem prime_oneHundredFortyFiveEM_13597 : Nat.Prime 13597 := by norm_num

private theorem prime_oneHundredFortyFiveEM_14009 : Nat.Prime 14009 := by norm_num

private theorem prime_oneHundredFortyFiveEM_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredFortyFiveEM_14717 : Nat.Prime 14717 := by norm_num

private theorem prime_oneHundredFortyFiveEM_14737 : Nat.Prime 14737 := by norm_num

private theorem prime_oneHundredFortyFiveEM_14747 : Nat.Prime 14747 := by norm_num

private theorem prime_oneHundredFortyFiveEM_15233 : Nat.Prime 15233 := by norm_num

private theorem prime_oneHundredFortyFiveEM_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredFortyFiveEM_15607 : Nat.Prime 15607 := by norm_num

private theorem prime_oneHundredFortyFiveEM_15791 : Nat.Prime 15791 := by norm_num

private theorem prime_oneHundredFortyFiveEM_16183 : Nat.Prime 16183 := by norm_num

private theorem prime_oneHundredFortyFiveEM_16249 : Nat.Prime 16249 := by norm_num

private theorem prime_oneHundredFortyFiveEM_16301 : Nat.Prime 16301 := by norm_num

private theorem prime_oneHundredFortyFiveEM_16427 : Nat.Prime 16427 := by norm_num

private theorem prime_oneHundredFortyFiveEM_16763 : Nat.Prime 16763 := by norm_num

private theorem prime_oneHundredFortyFiveEM_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFortyFiveEM_17573 : Nat.Prime 17573 := by norm_num

private theorem prime_oneHundredFortyFiveEM_18517 : Nat.Prime 18517 := by norm_num

private theorem prime_oneHundredFortyFiveEM_18587 : Nat.Prime 18587 := by norm_num

private theorem prime_oneHundredFortyFiveEM_19429 : Nat.Prime 19429 := by norm_num

private theorem prime_oneHundredFortyFiveEM_19463 : Nat.Prime 19463 := by norm_num

private theorem prime_oneHundredFortyFiveEM_19541 : Nat.Prime 19541 := by norm_num

private theorem prime_oneHundredFortyFiveEM_19973 : Nat.Prime 19973 := by norm_num

private theorem prime_oneHundredFortyFiveEM_20521 : Nat.Prime 20521 := by norm_num

private theorem prime_oneHundredFortyFiveEM_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFortyFiveEM_21283 : Nat.Prime 21283 := by norm_num

private theorem prime_oneHundredFortyFiveEM_21347 : Nat.Prime 21347 := by norm_num

private theorem prime_oneHundredFortyFiveEM_22447 : Nat.Prime 22447 := by norm_num

private theorem prime_oneHundredFortyFiveEM_22871 : Nat.Prime 22871 := by norm_num

private theorem prime_oneHundredFortyFiveEM_23291 : Nat.Prime 23291 := by norm_num

private theorem prime_oneHundredFortyFiveEM_24527 : Nat.Prime 24527 := by norm_num

private theorem prime_oneHundredFortyFiveEM_25057 : Nat.Prime 25057 := by norm_num

private theorem prime_oneHundredFortyFiveEM_25439 : Nat.Prime 25439 := by norm_num

private theorem prime_oneHundredFortyFiveEM_25633 : Nat.Prime 25633 := by norm_num

private theorem prime_oneHundredFortyFiveEM_25657 : Nat.Prime 25657 := by norm_num

private theorem prime_oneHundredFortyFiveEM_27259 : Nat.Prime 27259 := by norm_num

private theorem prime_oneHundredFortyFiveEM_27617 : Nat.Prime 27617 := by norm_num

private theorem prime_oneHundredFortyFiveEM_27847 : Nat.Prime 27847 := by norm_num

private theorem prime_oneHundredFortyFiveEM_27967 : Nat.Prime 27967 := by norm_num

private theorem prime_oneHundredFortyFiveEM_31039 : Nat.Prime 31039 := by norm_num

private theorem prime_oneHundredFortyFiveEM_34327 : Nat.Prime 34327 := by norm_num

private theorem prime_oneHundredFortyFiveEM_35801 : Nat.Prime 35801 := by norm_num

private theorem prime_oneHundredFortyFiveEM_37489 : Nat.Prime 37489 := by norm_num

private theorem prime_oneHundredFortyFiveEM_38047 : Nat.Prime 38047 := by norm_num

private theorem prime_oneHundredFortyFiveEM_39139 : Nat.Prime 39139 := by norm_num

private theorem prime_oneHundredFortyFiveEM_39461 : Nat.Prime 39461 := by norm_num

private theorem prime_oneHundredFortyFiveEM_40093 : Nat.Prime 40093 := by norm_num

private theorem prime_oneHundredFortyFiveEM_41257 : Nat.Prime 41257 := by norm_num

private theorem prime_oneHundredFortyFiveEM_42643 : Nat.Prime 42643 := by norm_num

private theorem prime_oneHundredFortyFiveEM_42667 : Nat.Prime 42667 := by norm_num

private theorem prime_oneHundredFortyFiveEM_43783 : Nat.Prime 43783 := by norm_num

private theorem prime_oneHundredFortyFiveEM_52147 : Nat.Prime 52147 := by norm_num

private theorem prime_oneHundredFortyFiveEM_52919 : Nat.Prime 52919 := by norm_num

private theorem prime_oneHundredFortyFiveEM_54037 : Nat.Prime 54037 := by norm_num

private theorem prime_oneHundredFortyFiveEM_54193 : Nat.Prime 54193 := by norm_num

private theorem prime_oneHundredFortyFiveEM_59377 : Nat.Prime 59377 := by norm_num

private theorem prime_oneHundredFortyFiveEM_60289 : Nat.Prime 60289 := by norm_num

private theorem prime_oneHundredFortyFiveEM_63577 : Nat.Prime 63577 := by norm_num

private theorem prime_oneHundredFortyFiveEM_66587 : Nat.Prime 66587 := by norm_num

private theorem prime_oneHundredFortyFiveEM_67723 : Nat.Prime 67723 := by norm_num

private theorem prime_oneHundredFortyFiveEM_68351 : Nat.Prime 68351 := by norm_num

private theorem prime_oneHundredFortyFiveEM_72053 : Nat.Prime 72053 := by norm_num

private theorem prime_oneHundredFortyFiveEM_79613 : Nat.Prime 79613 := by norm_num

private theorem prime_oneHundredFortyFiveEM_91009 : Nat.Prime 91009 := by norm_num

private theorem prime_oneHundredFortyFiveEM_92789 : Nat.Prime 92789 := by norm_num

private theorem prime_oneHundredFortyFiveEM_103963 : Nat.Prime 103963 := by norm_num

private theorem prime_oneHundredFortyFiveEM_108943 : Nat.Prime 108943 := by norm_num

private theorem prime_oneHundredFortyFiveEM_110753 : Nat.Prime 110753 := by norm_num

private theorem prime_oneHundredFortyFiveEM_113909 : Nat.Prime 113909 := by norm_num

private theorem prime_oneHundredFortyFiveEM_125617 : Nat.Prime 125617 := by norm_num

private theorem prime_oneHundredFortyFiveEM_126641 : Nat.Prime 126641 := by norm_num

private theorem prime_oneHundredFortyFiveEM_128213 : Nat.Prime 128213 := by norm_num

private theorem prime_oneHundredFortyFiveEM_129011 : Nat.Prime 129011 := by norm_num

private theorem prime_oneHundredFortyFiveEM_132421 : Nat.Prime 132421 := by norm_num

private theorem prime_oneHundredFortyFiveEM_133039 : Nat.Prime 133039 := by norm_num

private theorem prime_oneHundredFortyFiveEM_133073 : Nat.Prime 133073 := by norm_num

private theorem prime_oneHundredFortyFiveEM_137699 : Nat.Prime 137699 := by norm_num

private theorem prime_oneHundredFortyFiveEM_144839 : Nat.Prime 144839 := by norm_num

private theorem prime_oneHundredFortyFiveEM_150343 : Nat.Prime 150343 := by norm_num

private theorem prime_oneHundredFortyFiveEM_158243 : Nat.Prime 158243 := by norm_num

private theorem prime_oneHundredFortyFiveEM_158419 : Nat.Prime 158419 := by norm_num

private theorem prime_oneHundredFortyFiveEM_160403 : Nat.Prime 160403 := by norm_num

private theorem prime_oneHundredFortyFiveEM_163337 : Nat.Prime 163337 := by norm_num

private theorem prime_oneHundredFortyFiveEM_167249 : Nat.Prime 167249 := by norm_num

private theorem prime_oneHundredFortyFiveEM_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFortyFiveEM_177011 : Nat.Prime 177011 := by norm_num

private theorem prime_oneHundredFortyFiveEM_180337 : Nat.Prime 180337 := by norm_num

private theorem prime_oneHundredFortyFiveEM_184711 : Nat.Prime 184711 := by norm_num

private theorem prime_oneHundredFortyFiveEM_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredFortyFiveEM_188767 : Nat.Prime 188767 := by norm_num

private theorem prime_oneHundredFortyFiveEM_190591 : Nat.Prime 190591 := by norm_num

private theorem prime_oneHundredFortyFiveEM_190783 : Nat.Prime 190783 := by norm_num

private theorem prime_oneHundredFortyFiveEM_193951 : Nat.Prime 193951 := by norm_num

private theorem prime_oneHundredFortyFiveEM_200569 : Nat.Prime 200569 := by norm_num

private theorem prime_oneHundredFortyFiveEM_210109 : Nat.Prime 210109 := by norm_num

private theorem prime_oneHundredFortyFiveEM_221159 : Nat.Prime 221159 := by norm_num

private theorem prime_oneHundredFortyFiveEM_226397 : Nat.Prime 226397 := by norm_num

private theorem prime_oneHundredFortyFiveEM_235871 : Nat.Prime 235871 := by norm_num

private theorem prime_oneHundredFortyFiveEM_250993 : Nat.Prime 250993 := by norm_num

private theorem prime_oneHundredFortyFiveEM_265339 : Nat.Prime 265339 := by norm_num

private theorem prime_oneHundredFortyFiveEM_270407 : Nat.Prime 270407 := by norm_num

private theorem prime_oneHundredFortyFiveEM_284743 : Nat.Prime 284743 := by norm_num

private theorem prime_oneHundredFortyFiveEM_289987 : Nat.Prime 289987 := by norm_num

private theorem prime_oneHundredFortyFiveEM_291077 : Nat.Prime 291077 := by norm_num

private theorem prime_oneHundredFortyFiveEM_296287 : Nat.Prime 296287 := by norm_num

private theorem prime_oneHundredFortyFiveEM_319577 : Nat.Prime 319577 := by norm_num

private theorem prime_oneHundredFortyFiveEM_323251 : Nat.Prime 323251 := by norm_num

private theorem prime_oneHundredFortyFiveEM_345689 : Nat.Prime 345689 := by norm_num

private theorem prime_oneHundredFortyFiveEM_351259 : Nat.Prime 351259 := by norm_num

private theorem prime_oneHundredFortyFiveEM_355417 : Nat.Prime 355417 := by norm_num

private theorem prime_oneHundredFortyFiveEM_367219 : Nat.Prime 367219 := by norm_num

private theorem prime_oneHundredFortyFiveEM_367651 : Nat.Prime 367651 := by norm_num

private theorem prime_oneHundredFortyFiveEM_369661 : Nat.Prime 369661 := by norm_num

private theorem prime_oneHundredFortyFiveEM_392201 : Nat.Prime 392201 := by norm_num

private theorem prime_oneHundredFortyFiveEM_414769 : Nat.Prime 414769 := by norm_num

private theorem prime_oneHundredFortyFiveEM_415069 : Nat.Prime 415069 := by norm_num

private theorem prime_oneHundredFortyFiveEM_439123 : Nat.Prime 439123 := by norm_num

private theorem prime_oneHundredFortyFiveEM_446549 : Nat.Prime 446549 := by norm_num

private theorem prime_oneHundredFortyFiveEM_480059 : Nat.Prime 480059 := by norm_num

private theorem prime_oneHundredFortyFiveEM_510793 : Nat.Prime 510793 := by norm_num

private theorem prime_oneHundredFortyFiveEM_515887 : Nat.Prime 515887 := by norm_num

private theorem prime_oneHundredFortyFiveEM_553849 : Nat.Prime 553849 := by norm_num

private theorem prime_oneHundredFortyFiveEM_579353 : Nat.Prime 579353 := by norm_num

private theorem prime_oneHundredFortyFiveEM_591137 : Nat.Prime 591137 := by norm_num

private theorem prime_oneHundredFortyFiveEM_598981 : Nat.Prime 598981 := by norm_num

private theorem prime_oneHundredFortyFiveEM_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredFortyFiveEM_625199 : Nat.Prime 625199 := by norm_num

private theorem prime_oneHundredFortyFiveEM_664843 : Nat.Prime 664843 := by norm_num

private theorem prime_oneHundredFortyFiveEM_696481 : Nat.Prime 696481 := by norm_num

private theorem prime_oneHundredFortyFiveEM_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredFortyFiveEM_705127 : Nat.Prime 705127 := by norm_num

private theorem prime_oneHundredFortyFiveEM_730339 : Nat.Prime 730339 := by norm_num

private theorem prime_oneHundredFortyFiveEM_807473 : Nat.Prime 807473 := by norm_num

private theorem prime_oneHundredFortyFiveEM_818959 : Nat.Prime 818959 := by norm_num

private theorem prime_oneHundredFortyFiveEM_847673 : Nat.Prime 847673 := by norm_num

private theorem prime_oneHundredFortyFiveEM_899893 : Nat.Prime 899893 := by norm_num

private theorem prime_oneHundredFortyFiveEM_924527 : Nat.Prime 924527 := by norm_num

private theorem prime_oneHundredFortyFiveEM_941609 : Nat.Prime 941609 := by norm_num

private theorem prime_oneHundredFortyFiveEM_987713 : Nat.Prime 987713 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1068871 : Nat.Prime 1068871 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1069223 : Nat.Prime 1069223 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1097143 : Nat.Prime 1097143 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1190953 : Nat.Prime 1190953 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1225933 : Nat.Prime 1225933 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1376231 : Nat.Prime 1376231 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1484459 : Nat.Prime 1484459 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1525049 : Nat.Prime 1525049 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1559119 : Nat.Prime 1559119 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1559267 : Nat.Prime 1559267 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1610227 : Nat.Prime 1610227 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1629923 : Nat.Prime 1629923 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1746599 : Nat.Prime 1746599 := by norm_num

private theorem prime_oneHundredFortyFiveEM_1750499 : Nat.Prime 1750499 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2021843 : Nat.Prime 2021843 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2121653 : Nat.Prime 2121653 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2157017 : Nat.Prime 2157017 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2212187 : Nat.Prime 2212187 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2273489 : Nat.Prime 2273489 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2358401 : Nat.Prime 2358401 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2470603 : Nat.Prime 2470603 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2528989 : Nat.Prime 2528989 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2570219 : Nat.Prime 2570219 := by norm_num

private theorem prime_oneHundredFortyFiveEM_2682307 : Nat.Prime 2682307 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3048713 : Nat.Prime 3048713 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3127219 : Nat.Prime 3127219 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3262451 : Nat.Prime 3262451 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3321761 : Nat.Prime 3321761 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3537337 : Nat.Prime 3537337 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3562193 : Nat.Prime 3562193 := by norm_num

private theorem prime_oneHundredFortyFiveEM_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4010771 : Nat.Prime 4010771 := by norm_num

private theorem prime_oneHundredFortyFiveEM_4347659 : Nat.Prime 4347659 := by norm_num

private theorem prime_oneHundredFortyFiveEM_5105407 : Nat.Prime 5105407 := by norm_num

private theorem prime_oneHundredFortyFiveEM_6707117 : Nat.Prime 6707117 := by norm_num

private theorem prime_oneHundredFortyFiveEM_6951563 : Nat.Prime 6951563 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7053727 : Nat.Prime 7053727 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7172107 : Nat.Prime 7172107 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7535629 : Nat.Prime 7535629 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7543763 : Nat.Prime 7543763 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7628339 : Nat.Prime 7628339 := by norm_num

private theorem prime_oneHundredFortyFiveEM_7807421 : Nat.Prime 7807421 := by norm_num

private theorem prime_oneHundredFortyFiveEM_9363521 : Nat.Prime 9363521 := by norm_num

private theorem prime_oneHundredFortyFiveEM_10622309 : Nat.Prime 10622309 := by norm_num

private theorem prime_oneHundredFortyFiveEM_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFortyFiveEM_10835431 : Nat.Prime 10835431 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11126903 : Nat.Prime 11126903 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11211769 : Nat.Prime 11211769 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11649479 : Nat.Prime 11649479 := by norm_num

private theorem prime_oneHundredFortyFiveEM_11899117 : Nat.Prime 11899117 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12049657 : Nat.Prime 12049657 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12460867 : Nat.Prime 12460867 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12515401 : Nat.Prime 12515401 := by norm_num

private theorem prime_oneHundredFortyFiveEM_12989623 : Nat.Prime 12989623 := by norm_num

private theorem prime_oneHundredFortyFiveEM_13193179 : Nat.Prime 13193179 := by norm_num

private theorem prime_oneHundredFortyFiveEM_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredFortyFiveEM_14105627 : Nat.Prime 14105627 := by norm_num

private theorem prime_oneHundredFortyFiveEM_14111599 : Nat.Prime 14111599 := by norm_num

private theorem prime_oneHundredFortyFiveEM_14735723 : Nat.Prime 14735723 := by norm_num

private theorem prime_oneHundredFortyFiveEM_15249511 : Nat.Prime 15249511 := by norm_num

private theorem prime_oneHundredFortyFiveEM_16637081 : Nat.Prime 16637081 := by norm_num

private theorem prime_oneHundredFortyFiveEM_17181383 : Nat.Prime 17181383 := by norm_num

private theorem prime_oneHundredFortyFiveEM_17705953 : Nat.Prime 17705953 := by norm_num

private theorem prime_oneHundredFortyFiveEM_18019909 : Nat.Prime 18019909 := by norm_num

private theorem prime_oneHundredFortyFiveEM_19374647 : Nat.Prime 19374647 := by norm_num

private theorem prime_oneHundredFortyFiveEM_19908373 : Nat.Prime 19908373 := by norm_num

private theorem prime_oneHundredFortyFiveEM_21211217 : Nat.Prime 21211217 := by norm_num

private theorem prime_oneHundredFortyFiveEM_22467229 : Nat.Prime 22467229 := by norm_num

private theorem prime_oneHundredFortyFiveEM_22845079 : Nat.Prime 22845079 := by norm_num

private theorem prime_oneHundredFortyFiveEM_22946681 : Nat.Prime 22946681 := by norm_num

private theorem prime_oneHundredFortyFiveEM_23137109 : Nat.Prime 23137109 := by norm_num

private theorem prime_oneHundredFortyFiveEM_23335867 : Nat.Prime 23335867 := by norm_num

private theorem prime_oneHundredFortyFiveEM_23897323 : Nat.Prime 23897323 := by norm_num

private theorem prime_oneHundredFortyFiveEM_25099219 : Nat.Prime 25099219 := by norm_num

private theorem prime_oneHundredFortyFiveEM_26680321 : Nat.Prime 26680321 := by norm_num

private theorem prime_oneHundredFortyFiveEM_31602863 : Nat.Prime 31602863 := by
  apply lucas_primality 31602863 (5 : ZMod 31602863)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (41257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (41257, 1)] : List FactorBlock).map factorBlockValue).prod) = 31602863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_383
      · exact prime_oneHundredFortyFiveEM_41257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 31602863) ^ 15801431 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 31602863) ^ 82514 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 31602863) ^ 766 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_31699207 : Nat.Prime 31699207 := by
  apply lucas_primality 31699207 (3 : ZMod 31699207)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (22871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (22871, 1)] : List FactorBlock).map factorBlockValue).prod) = 31699207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_22871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31699207) ^ 15849603 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 31699207) ^ 10566402 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 31699207) ^ 4528458 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 31699207) ^ 2881746 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 31699207) ^ 1386 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_31921399 : Nat.Prime 31921399 := by
  apply lucas_primality 31921399 (6 : ZMod 31921399)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (591137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (591137, 1)] : List FactorBlock).map factorBlockValue).prod) = 31921399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_591137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 31921399) ^ 15960699 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 31921399) ^ 10640466 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 31921399) ^ 54 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_33857809 : Nat.Prime 33857809 := by
  apply lucas_primality 33857809 (7 : ZMod 33857809)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (643, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (643, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 33857809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_643
      · exact prime_oneHundredFortyFiveEM_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 33857809) ^ 16928904 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 33857809) ^ 11285936 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 33857809) ^ 52656 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 33857809) ^ 30864 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_34196527 : Nat.Prime 34196527 := by
  apply lucas_primality 34196527 (3 : ZMod 34196527)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (13, 1), (6959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (13, 1), (6959, 1)] : List FactorBlock).map factorBlockValue).prod) = 34196527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_6959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34196527) ^ 17098263 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 34196527) ^ 11398842 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 34196527) ^ 4885218 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 34196527) ^ 2630502 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 34196527) ^ 4914 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_35260279 : Nat.Prime 35260279 := by
  apply lucas_primality 35260279 (3 : ZMod 35260279)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (345689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (345689, 1)] : List FactorBlock).map factorBlockValue).prod) = 35260279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_345689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35260279) ^ 17630139 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35260279) ^ 11753426 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35260279) ^ 2074134 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 35260279) ^ 102 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_35877619 : Nat.Prime 35877619 := by
  apply lucas_primality 35877619 (2 : ZMod 35877619)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (284743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (284743, 1)] : List FactorBlock).map factorBlockValue).prod) = 35877619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_284743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35877619) ^ 17938809 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 35877619) ^ 11959206 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 35877619) ^ 5125374 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 35877619) ^ 126 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_36043529 : Nat.Prime 36043529 := by
  apply lucas_primality 36043529 (3 : ZMod 36043529)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (797, 1), (5653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (797, 1), (5653, 1)] : List FactorBlock).map factorBlockValue).prod) = 36043529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_797
      · exact prime_oneHundredFortyFiveEM_5653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36043529) ^ 18021764 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 36043529) ^ 45224 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 36043529) ^ 6376 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_37810391 : Nat.Prime 37810391 := by
  apply lucas_primality 37810391 (11 : ZMod 37810391)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (31, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (31, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) = 37810391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_31
      · exact prime_oneHundredFortyFiveEM_5303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 37810391) ^ 18905195 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 37810391) ^ 7562078 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 37810391) ^ 1643930 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 37810391) ^ 1219690 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 37810391) ^ 7130 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_45482783 : Nat.Prime 45482783 := by
  apply lucas_primality 45482783 (5 : ZMod 45482783)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (59377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (59377, 1)] : List FactorBlock).map factorBlockValue).prod) = 45482783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_383
      · exact prime_oneHundredFortyFiveEM_59377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 45482783) ^ 22741391 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 45482783) ^ 118754 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 45482783) ^ 766 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_45893363 : Nat.Prime 45893363 := by
  apply lucas_primality 45893363 (2 : ZMod 45893363)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22946681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22946681, 1)] : List FactorBlock).map factorBlockValue).prod) = 45893363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_22946681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 45893363) ^ 22946681 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 45893363) ^ 2 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_46322533 : Nat.Prime 46322533 := by
  apply lucas_primality 46322533 (5 : ZMod 46322533)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (67723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (67723, 1)] : List FactorBlock).map factorBlockValue).prod) = 46322533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_67723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 46322533) ^ 23161266 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 46322533) ^ 15440844 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 46322533) ^ 2438028 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 46322533) ^ 684 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_50493167 : Nat.Prime 50493167 := by
  apply lucas_primality 50493167 (5 : ZMod 50493167)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (319577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (319577, 1)] : List FactorBlock).map factorBlockValue).prod) = 50493167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_79
      · exact prime_oneHundredFortyFiveEM_319577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 50493167) ^ 25246583 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 50493167) ^ 639154 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 50493167) ^ 158 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_67892897 : Nat.Prime 67892897 := by
  apply lucas_primality 67892897 (3 : ZMod 67892897)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2121653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2121653, 1)] : List FactorBlock).map factorBlockValue).prod) = 67892897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_2121653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 67892897) ^ 33946448 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 67892897) ^ 32 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_72211021 : Nat.Prime 72211021 := by
  apply lucas_primality 72211021 (6 : ZMod 72211021)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (19, 1), (9049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (19, 1), (9049, 1)] : List FactorBlock).map factorBlockValue).prod) = 72211021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_9049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 72211021) ^ 36105510 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 72211021) ^ 24070340 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 72211021) ^ 14442204 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 72211021) ^ 10315860 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 72211021) ^ 3800580 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 72211021) ^ 7980 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_72297943 : Nat.Prime 72297943 := by
  apply lucas_primality 72297943 (5 : ZMod 72297943)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12049657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12049657, 1)] : List FactorBlock).map factorBlockValue).prod) = 72297943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_12049657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 72297943) ^ 36148971 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 72297943) ^ 24099314 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 72297943) ^ 6 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_78646559 : Nat.Prime 78646559 := by
  apply lucas_primality 78646559 (17 : ZMod 78646559)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (553849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (553849, 1)] : List FactorBlock).map factorBlockValue).prod) = 78646559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_71
      · exact prime_oneHundredFortyFiveEM_553849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 78646559) ^ 39323279 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (17 : ZMod 78646559) ^ 1107698 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (17 : ZMod 78646559) ^ 142 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_82130771 : Nat.Prime 82130771 := by
  apply lucas_primality 82130771 (2 : ZMod 82130771)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (103963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (103963, 1)] : List FactorBlock).map factorBlockValue).prod) = 82130771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_79
      · exact prime_oneHundredFortyFiveEM_103963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82130771) ^ 41065385 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 82130771) ^ 16426154 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 82130771) ^ 1039630 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 82130771) ^ 790 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_83782499 : Nat.Prime 83782499 := by
  apply lucas_primality 83782499 (2 : ZMod 83782499)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (379, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (379, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) = 83782499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_107
      · exact prime_oneHundredFortyFiveEM_379
      · exact prime_oneHundredFortyFiveEM_1033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83782499) ^ 41891249 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83782499) ^ 783014 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83782499) ^ 221062 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83782499) ^ 81106 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_85849273 : Nat.Prime 85849273 := by
  apply lucas_primality 85849273 (7 : ZMod 85849273)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (109, 1), (10939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (109, 1), (10939, 1)] : List FactorBlock).map factorBlockValue).prod) = 85849273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_109
      · exact prime_oneHundredFortyFiveEM_10939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 85849273) ^ 42924636 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 85849273) ^ 28616424 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 85849273) ^ 787608 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 85849273) ^ 7848 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_90229301 : Nat.Prime 90229301 := by
  apply lucas_primality 90229301 (2 : ZMod 90229301)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (83, 1), (1553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (83, 1), (1553, 1)] : List FactorBlock).map factorBlockValue).prod) = 90229301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_83
      · exact prime_oneHundredFortyFiveEM_1553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90229301) ^ 45114650 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 90229301) ^ 18045860 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 90229301) ^ 12889900 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 90229301) ^ 1087100 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 90229301) ^ 58100 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_99539827 : Nat.Prime 99539827 := by
  apply lucas_primality 99539827 (3 : ZMod 99539827)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (126641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (126641, 1)] : List FactorBlock).map factorBlockValue).prod) = 99539827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_131
      · exact prime_oneHundredFortyFiveEM_126641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 99539827) ^ 49769913 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 99539827) ^ 33179942 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 99539827) ^ 759846 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 99539827) ^ 786 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_101481487 : Nat.Prime 101481487 := by
  apply lucas_primality 101481487 (3 : ZMod 101481487)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (54037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (54037, 1)] : List FactorBlock).map factorBlockValue).prod) = 101481487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_313
      · exact prime_oneHundredFortyFiveEM_54037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101481487) ^ 50740743 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 101481487) ^ 33827162 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 101481487) ^ 324222 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 101481487) ^ 1878 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_116276113 : Nat.Prime 116276113 := by
  apply lucas_primality 116276113 (5 : ZMod 116276113)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (807473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (807473, 1)] : List FactorBlock).map factorBlockValue).prod) = 116276113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_807473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 116276113) ^ 58138056 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 116276113) ^ 38758704 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 116276113) ^ 144 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_117934951 : Nat.Prime 117934951 := by
  apply lucas_primality 117934951 (23 : ZMod 117934951)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (6607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (6607, 1)] : List FactorBlock).map factorBlockValue).prod) = 117934951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_6607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 117934951) ^ 58967475 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 39311650 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 23586990 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 16847850 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 6937350 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 117934951) ^ 17850 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_120323131 : Nat.Prime 120323131 := by
  apply lucas_primality 120323131 (10 : ZMod 120323131)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4010771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4010771, 1)] : List FactorBlock).map factorBlockValue).prod) = 120323131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_4010771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 120323131) ^ 60161565 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 120323131) ^ 40107710 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 120323131) ^ 24064626 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 120323131) ^ 30 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_120796301 : Nat.Prime 120796301 := by
  apply lucas_primality 120796301 (3 : ZMod 120796301)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (19, 1), (63577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (19, 1), (63577, 1)] : List FactorBlock).map factorBlockValue).prod) = 120796301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_63577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120796301) ^ 60398150 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 120796301) ^ 24159260 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 120796301) ^ 6357700 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 120796301) ^ 1900 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_121233859 : Nat.Prime 121233859 := by
  apply lucas_primality 121233859 (2 : ZMod 121233859)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (163, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (163, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 121233859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_113
      · exact prime_oneHundredFortyFiveEM_163
      · exact prime_oneHundredFortyFiveEM_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121233859) ^ 60616929 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121233859) ^ 40411286 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121233859) ^ 1072866 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121233859) ^ 743766 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121233859) ^ 110514 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_121520171 : Nat.Prime 121520171 := by
  apply lucas_primality 121520171 (2 : ZMod 121520171)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (101, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (101, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 121520171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_79
      · exact prime_oneHundredFortyFiveEM_101
      · exact prime_oneHundredFortyFiveEM_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121520171) ^ 60760085 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121520171) ^ 24304034 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121520171) ^ 1538230 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121520171) ^ 1203170 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 121520171) ^ 79790 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_125154011 : Nat.Prime 125154011 := by
  apply lucas_primality 125154011 (6 : ZMod 125154011)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12515401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12515401, 1)] : List FactorBlock).map factorBlockValue).prod) = 125154011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_12515401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 125154011) ^ 62577005 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 125154011) ^ 25030802 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 125154011) ^ 10 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_138185629 : Nat.Prime 138185629 := by
  apply lucas_primality 138185629 (2 : ZMod 138185629)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 1), (31039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 1), (31039, 1)] : List FactorBlock).map factorBlockValue).prod) = 138185629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_53
      · exact prime_oneHundredFortyFiveEM_31039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 138185629) ^ 69092814 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 138185629) ^ 46061876 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 138185629) ^ 19740804 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 138185629) ^ 2607276 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 138185629) ^ 4452 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_145064807 : Nat.Prime 145064807 := by
  apply lucas_primality 145064807 (5 : ZMod 145064807)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (743, 1), (2381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (743, 1), (2381, 1)] : List FactorBlock).map factorBlockValue).prod) = 145064807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_41
      · exact prime_oneHundredFortyFiveEM_743
      · exact prime_oneHundredFortyFiveEM_2381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 145064807) ^ 72532403 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 145064807) ^ 3538166 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 145064807) ^ 195242 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 145064807) ^ 60926 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_150373913 : Nat.Prime 150373913 := by
  apply lucas_primality 150373913 (3 : ZMod 150373913)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (487, 1), (2969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (487, 1), (2969, 1)] : List FactorBlock).map factorBlockValue).prod) = 150373913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_487
      · exact prime_oneHundredFortyFiveEM_2969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 150373913) ^ 75186956 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 150373913) ^ 11567224 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 150373913) ^ 308776 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 150373913) ^ 50648 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_151008061 : Nat.Prime 151008061 := by
  apply lucas_primality 151008061 (14 : ZMod 151008061)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (257, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (257, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 151008061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_257
      · exact prime_oneHundredFortyFiveEM_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 151008061) ^ 75504030 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 151008061) ^ 50336020 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 151008061) ^ 30201612 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 151008061) ^ 21572580 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 151008061) ^ 587580 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 151008061) ^ 107940 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_166051843 : Nat.Prime 166051843 := by
  apply lucas_primality 166051843 (3 : ZMod 166051843)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (59, 1), (42643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (59, 1), (42643, 1)] : List FactorBlock).map factorBlockValue).prod) = 166051843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_42643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 166051843) ^ 83025921 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 166051843) ^ 55350614 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 166051843) ^ 15095622 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 166051843) ^ 2814438 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 166051843) ^ 3894 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_169347799 : Nat.Prime 169347799 := by
  apply lucas_primality 169347799 (11 : ZMod 169347799)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (347, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (347, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) = 169347799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_347
      · exact prime_oneHundredFortyFiveEM_1427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 169347799) ^ 84673899 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 169347799) ^ 56449266 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 169347799) ^ 8913042 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 169347799) ^ 488034 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 169347799) ^ 118674 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_178151971 : Nat.Prime 178151971 := by
  apply lucas_primality 178151971 (2 : ZMod 178151971)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (144839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (144839, 1)] : List FactorBlock).map factorBlockValue).prod) = 178151971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_41
      · exact prime_oneHundredFortyFiveEM_144839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178151971) ^ 89075985 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178151971) ^ 59383990 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178151971) ^ 35630394 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178151971) ^ 4345170 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 178151971) ^ 1230 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_179032871 : Nat.Prime 179032871 := by
  apply lucas_primality 179032871 (29 : ZMod 179032871)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (313, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (313, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 179032871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_47
      · exact prime_oneHundredFortyFiveEM_313
      · exact prime_oneHundredFortyFiveEM_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 179032871) ^ 89516435 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 179032871) ^ 35806574 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 179032871) ^ 3809210 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 179032871) ^ 571990 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 179032871) ^ 147110 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_200770543 : Nat.Prime 200770543 := by
  apply lucas_primality 200770543 (3 : ZMod 200770543)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (23, 1), (3299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (23, 1), (3299, 1)] : List FactorBlock).map factorBlockValue).prod) = 200770543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_3299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 200770543) ^ 100385271 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 200770543) ^ 66923514 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 200770543) ^ 28681506 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 200770543) ^ 8729154 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 200770543) ^ 60858 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_272490791 : Nat.Prime 272490791 := by
  apply lucas_primality 272490791 (11 : ZMod 272490791)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (13, 1), (17, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (13, 1), (17, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) = 272490791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_1019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 272490791) ^ 136245395 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 272490791) ^ 54498158 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 272490791) ^ 24771890 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 272490791) ^ 20960830 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 272490791) ^ 16028870 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 272490791) ^ 267410 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_290256851 : Nat.Prime 290256851 := by
  apply lucas_primality 290256851 (14 : ZMod 290256851)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (446549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (446549, 1)] : List FactorBlock).map factorBlockValue).prod) = 290256851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_446549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 290256851) ^ 145128425 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 290256851) ^ 58051370 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 290256851) ^ 22327450 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 290256851) ^ 650 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_290382289 : Nat.Prime 290382289 := by
  apply lucas_primality 290382289 (11 : ZMod 290382289)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (67, 1), (12899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (67, 1), (12899, 1)] : List FactorBlock).map factorBlockValue).prod) = 290382289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_67
      · exact prime_oneHundredFortyFiveEM_12899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 290382289) ^ 145191144 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 290382289) ^ 96794096 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 290382289) ^ 41483184 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 290382289) ^ 4334064 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 290382289) ^ 22512 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_309928999 : Nat.Prime 309928999 := by
  apply lucas_primality 309928999 (3 : ZMod 309928999)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (317, 1), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (317, 1), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) = 309928999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_47
      · exact prime_oneHundredFortyFiveEM_317
      · exact prime_oneHundredFortyFiveEM_3467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 309928999) ^ 154964499 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 309928999) ^ 103309666 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 309928999) ^ 6594234 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 309928999) ^ 977694 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 309928999) ^ 89394 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_358776191 : Nat.Prime 358776191 := by
  apply lucas_primality 358776191 (7 : ZMod 358776191)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (35877619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (35877619, 1)] : List FactorBlock).map factorBlockValue).prod) = 358776191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_35877619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 358776191) ^ 179388095 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 358776191) ^ 71755238 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 358776191) ^ 10 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_12539
      · exact prime_oneHundredFortyFiveEM_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_364916653 : Nat.Prime 364916653 := by
  apply lucas_primality 364916653 (2 : ZMod 364916653)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (107, 1), (4817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (107, 1), (4817, 1)] : List FactorBlock).map factorBlockValue).prod) = 364916653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_107
      · exact prime_oneHundredFortyFiveEM_4817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 364916653) ^ 182458326 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 364916653) ^ 121638884 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 364916653) ^ 6185028 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 364916653) ^ 3410436 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 364916653) ^ 75756 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_384668593 : Nat.Prime 384668593 := by
  apply lucas_primality 384668593 (5 : ZMod 384668593)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (11, 1), (199, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (11, 1), (199, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 384668593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_199
      · exact prime_oneHundredFortyFiveEM_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 384668593) ^ 192334296 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 384668593) ^ 128222864 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 384668593) ^ 54952656 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 384668593) ^ 34969872 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 384668593) ^ 1933008 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 384668593) ^ 735504 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_394142149 : Nat.Prime 394142149 := by
  apply lucas_primality 394142149 (2 : ZMod 394142149)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2843, 1), (3851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2843, 1), (3851, 1)] : List FactorBlock).map factorBlockValue).prod) = 394142149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_2843
      · exact prime_oneHundredFortyFiveEM_3851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 394142149) ^ 197071074 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 394142149) ^ 131380716 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 394142149) ^ 138636 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 394142149) ^ 102348 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_398159309 : Nat.Prime 398159309 := by
  apply lucas_primality 398159309 (2 : ZMod 398159309)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (99539827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (99539827, 1)] : List FactorBlock).map factorBlockValue).prod) = 398159309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_99539827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 398159309) ^ 199079654 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 398159309) ^ 4 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_403945337 : Nat.Prime 403945337 := by
  apply lucas_primality 403945337 (3 : ZMod 403945337)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (50493167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (50493167, 1)] : List FactorBlock).map factorBlockValue).prod) = 403945337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_50493167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 403945337) ^ 201972668 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 403945337) ^ 8 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_406538471 : Nat.Prime 406538471 := by
  apply lucas_primality 406538471 (11 : ZMod 406538471)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (3127219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (3127219, 1)] : List FactorBlock).map factorBlockValue).prod) = 406538471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_3127219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 406538471) ^ 203269235 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 406538471) ^ 81307694 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 406538471) ^ 31272190 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 406538471) ^ 130 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_423620759 : Nat.Prime 423620759 := by
  apply lucas_primality 423620759 (7 : ZMod 423620759)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (1750499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (1750499, 1)] : List FactorBlock).map factorBlockValue).prod) = 423620759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_1750499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 423620759) ^ 211810379 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 423620759) ^ 38510978 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 423620759) ^ 242 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_424416887 : Nat.Prime 424416887 := by
  apply lucas_primality 424416887 (5 : ZMod 424416887)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (92789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (92789, 1)] : List FactorBlock).map factorBlockValue).prod) = 424416887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_2287
      · exact prime_oneHundredFortyFiveEM_92789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 424416887) ^ 212208443 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 424416887) ^ 185578 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 424416887) ^ 4574 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_426986309 : Nat.Prime 426986309 := by
  apply lucas_primality 426986309 (2 : ZMod 426986309)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (15249511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (15249511, 1)] : List FactorBlock).map factorBlockValue).prod) = 426986309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_15249511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 426986309) ^ 213493154 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 426986309) ^ 60998044 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 426986309) ^ 28 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_451061227 : Nat.Prime 451061227 := by
  apply lucas_primality 451061227 (3 : ZMod 451061227)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (503, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (503, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 451061227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_503
      · exact prime_oneHundredFortyFiveEM_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 451061227) ^ 225530613 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 150353742 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 64437318 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 41005566 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 896742 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 451061227) ^ 697158 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_490119073 : Nat.Prime 490119073 := by
  apply lucas_primality 490119073 (5 : ZMod 490119073)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5105407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5105407, 1)] : List FactorBlock).map factorBlockValue).prod) = 490119073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5105407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 490119073) ^ 245059536 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 490119073) ^ 163373024 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 490119073) ^ 96 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_544981583 : Nat.Prime 544981583 := by
  apply lucas_primality 544981583 (5 : ZMod 544981583)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (272490791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (272490791, 1)] : List FactorBlock).map factorBlockValue).prod) = 544981583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_272490791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 544981583) ^ 272490791 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 544981583) ^ 2 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_545793397 : Nat.Prime 545793397 := by
  apply lucas_primality 545793397 (6 : ZMod 545793397)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (45482783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (45482783, 1)] : List FactorBlock).map factorBlockValue).prod) = 545793397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_45482783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 545793397) ^ 272896698 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 545793397) ^ 181931132 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 545793397) ^ 12 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_564363889 : Nat.Prime 564363889 := by
  apply lucas_primality 564363889 (7 : ZMod 564363889)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (1068871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (1068871, 1)] : List FactorBlock).map factorBlockValue).prod) = 564363889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_1068871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 564363889) ^ 282181944 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 564363889) ^ 188121296 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 564363889) ^ 51305808 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 564363889) ^ 528 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_573199883 : Nat.Prime 573199883 := by
  apply lucas_primality 573199883 (2 : ZMod 573199883)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (12460867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (12460867, 1)] : List FactorBlock).map factorBlockValue).prod) = 573199883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_12460867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 573199883) ^ 286599941 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 573199883) ^ 24921734 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 573199883) ^ 46 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_580039043 : Nat.Prime 580039043 := by
  apply lucas_primality 580039043 (2 : ZMod 580039043)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2657, 1), (9923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2657, 1), (9923, 1)] : List FactorBlock).map factorBlockValue).prod) = 580039043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_2657
      · exact prime_oneHundredFortyFiveEM_9923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 580039043) ^ 290019521 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 580039043) ^ 52730822 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 580039043) ^ 218306 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 580039043) ^ 58454 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_582888253 : Nat.Prime 582888253 := by
  apply lucas_primality 582888253 (2 : ZMod 582888253)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4903, 1), (9907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4903, 1), (9907, 1)] : List FactorBlock).map factorBlockValue).prod) = 582888253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_4903
      · exact prime_oneHundredFortyFiveEM_9907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 582888253) ^ 291444126 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 582888253) ^ 194296084 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 582888253) ^ 118884 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 582888253) ^ 58836 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_625233397 : Nat.Prime 625233397 := by
  apply lucas_primality 625233397 (6 : ZMod 625233397)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (291077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (291077, 1)] : List FactorBlock).map factorBlockValue).prod) = 625233397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_179
      · exact prime_oneHundredFortyFiveEM_291077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 625233397) ^ 312616698 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 625233397) ^ 208411132 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 625233397) ^ 3492924 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 625233397) ^ 2148 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_677911001 : Nat.Prime 677911001 := by
  apply lucas_primality 677911001 (3 : ZMod 677911001)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (13, 1), (52147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (13, 1), (52147, 1)] : List FactorBlock).map factorBlockValue).prod) = 677911001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_52147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 677911001) ^ 338955500 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 677911001) ^ 135582200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 677911001) ^ 52147000 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 677911001) ^ 13000 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_17203
      · exact prime_oneHundredFortyFiveEM_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_738464789 : Nat.Prime 738464789 := by
  apply lucas_primality 738464789 (2 : ZMod 738464789)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (2528989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (2528989, 1)] : List FactorBlock).map factorBlockValue).prod) = 738464789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_73
      · exact prime_oneHundredFortyFiveEM_2528989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 738464789) ^ 369232394 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 738464789) ^ 10115956 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 738464789) ^ 292 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_847241519 : Nat.Prime 847241519 := by
  apply lucas_primality 847241519 (11 : ZMod 847241519)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (423620759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (423620759, 1)] : List FactorBlock).map factorBlockValue).prod) = 847241519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_423620759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 847241519) ^ 423620759 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 847241519) ^ 2 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_853972619 : Nat.Prime 853972619 := by
  apply lucas_primality 853972619 (2 : ZMod 853972619)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (426986309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (426986309, 1)] : List FactorBlock).map factorBlockValue).prod) = 853972619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_426986309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 853972619) ^ 426986309 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 853972619) ^ 2 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_905238673 : Nat.Prime 905238673 := by
  apply lucas_primality 905238673 (5 : ZMod 905238673)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (41, 2), (863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (41, 2), (863, 1)] : List FactorBlock).map factorBlockValue).prod) = 905238673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_41
      · exact prime_oneHundredFortyFiveEM_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 905238673) ^ 452619336 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 905238673) ^ 301746224 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 905238673) ^ 69633744 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 905238673) ^ 22078992 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 905238673) ^ 1048944 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_958824821 : Nat.Prime 958824821 := by
  apply lucas_primality 958824821 (2 : ZMod 958824821)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (173, 1), (16301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (173, 1), (16301, 1)] : List FactorBlock).map factorBlockValue).prod) = 958824821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_173
      · exact prime_oneHundredFortyFiveEM_16301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 958824821) ^ 479412410 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 958824821) ^ 191764964 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 958824821) ^ 56401460 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 958824821) ^ 5542340 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 958824821) ^ 58820 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_996311059 : Nat.Prime 996311059 := by
  apply lucas_primality 996311059 (2 : ZMod 996311059)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (166051843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (166051843, 1)] : List FactorBlock).map factorBlockValue).prod) = 996311059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_166051843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 996311059) ^ 498155529 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 996311059) ^ 332103686 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 996311059) ^ 6 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1079547257 : Nat.Prime 1079547257 := by
  apply lucas_primality 1079547257 (3 : ZMod 1079547257)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (2212187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (2212187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079547257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_61
      · exact prime_oneHundredFortyFiveEM_2212187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1079547257) ^ 539773628 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1079547257) ^ 17697496 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1079547257) ^ 488 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1101440713 : Nat.Prime 1101440713 := by
  apply lucas_primality 1101440713 (10 : ZMod 1101440713)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (45893363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (45893363, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101440713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_45893363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1101440713) ^ 550720356 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1101440713) ^ 367146904 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1101440713) ^ 24 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1132689223 : Nat.Prime 1132689223 := by
  apply lucas_primality 1132689223 (3 : ZMod 1132689223)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (31, 1), (289987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (31, 1), (289987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1132689223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_31
      · exact prime_oneHundredFortyFiveEM_289987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1132689223) ^ 566344611 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1132689223) ^ 377563074 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1132689223) ^ 161812746 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1132689223) ^ 36538362 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1132689223) ^ 3906 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1161529157 : Nat.Prime 1161529157 := by
  apply lucas_primality 1161529157 (2 : ZMod 1161529157)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (290382289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (290382289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1161529157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_290382289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1161529157) ^ 580764578 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1161529157) ^ 4 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1267727987 : Nat.Prime 1267727987 := by
  apply lucas_primality 1267727987 (2 : ZMod 1267727987)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (1484459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (1484459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1267727987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_61
      · exact prime_oneHundredFortyFiveEM_1484459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1267727987) ^ 633863993 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267727987) ^ 181103998 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267727987) ^ 20782426 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267727987) ^ 854 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1402675697 : Nat.Prime 1402675697 := by
  apply lucas_primality 1402675697 (3 : ZMod 1402675697)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (173, 1), (313, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (173, 1), (313, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1402675697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_173
      · exact prime_oneHundredFortyFiveEM_313
      · exact prime_oneHundredFortyFiveEM_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1402675697) ^ 701337848 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1402675697) ^ 8107952 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1402675697) ^ 4481392 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1402675697) ^ 866384 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1669035451 : Nat.Prime 1669035451 := by
  apply lucas_primality 1669035451 (3 : ZMod 1669035451)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11126903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11126903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1669035451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_11126903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1669035451) ^ 834517725 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1669035451) ^ 556345150 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1669035451) ^ 333807090 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1669035451) ^ 150 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1705568869 : Nat.Prime 1705568869 := by
  apply lucas_primality 1705568869 (2 : ZMod 1705568869)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5479, 1), (8647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5479, 1), (8647, 1)] : List FactorBlock).map factorBlockValue).prod) = 1705568869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5479
      · exact prime_oneHundredFortyFiveEM_8647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1705568869) ^ 852784434 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1705568869) ^ 568522956 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1705568869) ^ 311292 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1705568869) ^ 197244 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1936604699 : Nat.Prime 1936604699 := by
  apply lucas_primality 1936604699 (2 : ZMod 1936604699)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (223, 1), (10169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (223, 1), (10169, 1)] : List FactorBlock).map factorBlockValue).prod) = 1936604699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_61
      · exact prime_oneHundredFortyFiveEM_223
      · exact prime_oneHundredFortyFiveEM_10169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1936604699) ^ 968302349 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1936604699) ^ 276657814 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1936604699) ^ 31747618 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1936604699) ^ 8684326 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1936604699) ^ 190442 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2014314619 : Nat.Prime 2014314619 := by
  apply lucas_primality 2014314619 (7 : ZMod 2014314619)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (7807421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (7807421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2014314619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_43
      · exact prime_oneHundredFortyFiveEM_7807421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2014314619) ^ 1007157309 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2014314619) ^ 671438206 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2014314619) ^ 46844526 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 2014314619) ^ 258 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2123067029 : Nat.Prime 2123067029 := by
  apply lucas_primality 2123067029 (2 : ZMod 2123067029)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (3562193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (3562193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2123067029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_149
      · exact prime_oneHundredFortyFiveEM_3562193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2123067029) ^ 1061533514 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2123067029) ^ 14248772 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2123067029) ^ 596 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2554578179 : Nat.Prime 2554578179 := by
  apply lucas_primality 2554578179 (2 : ZMod 2554578179)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7963, 1), (160403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7963, 1), (160403, 1)] : List FactorBlock).map factorBlockValue).prod) = 2554578179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7963
      · exact prime_oneHundredFortyFiveEM_160403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2554578179) ^ 1277289089 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2554578179) ^ 320806 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2554578179) ^ 15926 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2756388629 : Nat.Prime 2756388629 := by
  apply lucas_primality 2756388629 (10 : ZMod 2756388629)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (251, 1), (392201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (251, 1), (392201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2756388629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_251
      · exact prime_oneHundredFortyFiveEM_392201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2756388629) ^ 1378194314 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2756388629) ^ 393769804 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2756388629) ^ 10981628 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 2756388629) ^ 7028 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_3258859057 : Nat.Prime 3258859057 := by
  apply lucas_primality 3258859057 (5 : ZMod 3258859057)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (67892897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (67892897, 1)] : List FactorBlock).map factorBlockValue).prod) = 3258859057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_67892897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3258859057) ^ 1629429528 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3258859057) ^ 1086286352 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3258859057) ^ 48 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_3751400383 : Nat.Prime 3751400383 := by
  apply lucas_primality 3751400383 (3 : ZMod 3751400383)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (625233397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (625233397, 1)] : List FactorBlock).map factorBlockValue).prod) = 3751400383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_625233397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3751400383) ^ 1875700191 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3751400383) ^ 1250466794 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3751400383) ^ 6 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_3876540901 : Nat.Prime 3876540901 := by
  apply lucas_primality 3876540901 (2 : ZMod 3876540901)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (73, 1), (177011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (73, 1), (177011, 1)] : List FactorBlock).map factorBlockValue).prod) = 3876540901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_73
      · exact prime_oneHundredFortyFiveEM_177011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3876540901) ^ 1938270450 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3876540901) ^ 1292180300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3876540901) ^ 775308180 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3876540901) ^ 53103300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3876540901) ^ 21900 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_4167246857 : Nat.Prime 4167246857 := by
  apply lucas_primality 4167246857 (3 : ZMod 4167246857)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (269, 1), (113909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (269, 1), (113909, 1)] : List FactorBlock).map factorBlockValue).prod) = 4167246857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_269
      · exact prime_oneHundredFortyFiveEM_113909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4167246857) ^ 2083623428 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4167246857) ^ 245132168 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4167246857) ^ 15491624 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4167246857) ^ 36584 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_4171670879 : Nat.Prime 4171670879 := by
  apply lucas_primality 4171670879 (17 : ZMod 4171670879)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (967, 1), (2157017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (967, 1), (2157017, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171670879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_967
      · exact prime_oneHundredFortyFiveEM_2157017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 4171670879) ^ 2085835439 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (17 : ZMod 4171670879) ^ 4314034 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (17 : ZMod 4171670879) ^ 1934 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_4318759631 : Nat.Prime 4318759631 := by
  apply lucas_primality 4318759631 (7 : ZMod 4318759631)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (277, 1), (1559119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (277, 1), (1559119, 1)] : List FactorBlock).map factorBlockValue).prod) = 4318759631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_277
      · exact prime_oneHundredFortyFiveEM_1559119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4318759631) ^ 2159379815 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 4318759631) ^ 863751926 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 4318759631) ^ 15591190 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 4318759631) ^ 2770 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_5293816793 : Nat.Prime 5293816793 := by
  apply lucas_primality 5293816793 (3 : ZMod 5293816793)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (1451, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (1451, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod) = 5293816793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_1451
      · exact prime_oneHundredFortyFiveEM_3769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5293816793) ^ 2646908396 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5293816793) ^ 481256072 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5293816793) ^ 3648392 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5293816793) ^ 1404568 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_31
      · exact prime_oneHundredFortyFiveEM_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_7121471219 : Nat.Prime 7121471219 := by
  apply lucas_primality 7121471219 (2 : ZMod 7121471219)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (59, 1), (1201, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (59, 1), (1201, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) = 7121471219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_31
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_1201
      · exact prime_oneHundredFortyFiveEM_1621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7121471219) ^ 3560735609 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7121471219) ^ 229724878 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7121471219) ^ 120702902 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7121471219) ^ 5929618 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7121471219) ^ 4393258 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_7462005923 : Nat.Prime 7462005923 := by
  apply lucas_primality 7462005923 (2 : ZMod 7462005923)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14009, 1), (38047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14009, 1), (38047, 1)] : List FactorBlock).map factorBlockValue).prod) = 7462005923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_14009
      · exact prime_oneHundredFortyFiveEM_38047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7462005923) ^ 3731002961 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7462005923) ^ 1066000846 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7462005923) ^ 532658 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7462005923) ^ 196126 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_8138142497 : Nat.Prime 8138142497 := by
  apply lucas_primality 8138142497 (3 : ZMod 8138142497)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 2), (47, 1), (197, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 2), (47, 1), (197, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 8138142497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_47
      · exact prime_oneHundredFortyFiveEM_197
      · exact prime_oneHundredFortyFiveEM_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8138142497) ^ 4069071248 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138142497) ^ 739831136 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138142497) ^ 173151968 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138142497) ^ 41310368 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138142497) ^ 35850848 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_9267907991 : Nat.Prime 9267907991 := by
  apply lucas_primality 9267907991 (11 : ZMod 9267907991)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (401, 1), (210109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (401, 1), (210109, 1)] : List FactorBlock).map factorBlockValue).prod) = 9267907991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_401
      · exact prime_oneHundredFortyFiveEM_210109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9267907991) ^ 4633953995 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 9267907991) ^ 1853581598 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 9267907991) ^ 842537090 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 9267907991) ^ 23111990 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 9267907991) ^ 44110 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_9935748359 : Nat.Prime 9935748359 := by
  apply lucas_primality 9935748359 (11 : ZMod 9935748359)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (151, 1), (369661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (151, 1), (369661, 1)] : List FactorBlock).map factorBlockValue).prod) = 9935748359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_89
      · exact prime_oneHundredFortyFiveEM_151
      · exact prime_oneHundredFortyFiveEM_369661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 9935748359) ^ 4967874179 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 9935748359) ^ 111637622 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 9935748359) ^ 65799658 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 9935748359) ^ 26878 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_11130243337 : Nat.Prime 11130243337 := by
  apply lucas_primality 11130243337 (5 : ZMod 11130243337)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (47, 1), (1493, 1), (2203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (47, 1), (1493, 1), (2203, 1)] : List FactorBlock).map factorBlockValue).prod) = 11130243337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_47
      · exact prime_oneHundredFortyFiveEM_1493
      · exact prime_oneHundredFortyFiveEM_2203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11130243337) ^ 5565121668 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11130243337) ^ 3710081112 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11130243337) ^ 236813688 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11130243337) ^ 7454952 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11130243337) ^ 5052312 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_14909685773 : Nat.Prime 14909685773 := by
  apply lucas_primality 14909685773 (2 : ZMod 14909685773)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (34196527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (34196527, 1)] : List FactorBlock).map factorBlockValue).prod) = 14909685773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_109
      · exact prime_oneHundredFortyFiveEM_34196527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14909685773) ^ 7454842886 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14909685773) ^ 136786108 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14909685773) ^ 436 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_18522282301 : Nat.Prime 18522282301 := by
  apply lucas_primality 18522282301 (6 : ZMod 18522282301)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (191, 1), (323251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (191, 1), (323251, 1)] : List FactorBlock).map factorBlockValue).prod) = 18522282301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_191
      · exact prime_oneHundredFortyFiveEM_323251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 18522282301) ^ 9261141150 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 18522282301) ^ 6174094100 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 18522282301) ^ 3704456460 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 18522282301) ^ 96975300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 18522282301) ^ 57300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_27077876857 : Nat.Prime 27077876857 := by
  apply lucas_primality 27077876857 (5 : ZMod 27077876857)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 8), (515887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 8), (515887, 1)] : List FactorBlock).map factorBlockValue).prod) = 27077876857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_515887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 27077876857) ^ 13538938428 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 27077876857) ^ 9025958952 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 27077876857) ^ 52488 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_31597729523 : Nat.Prime 31597729523 := by
  apply lucas_primality 31597729523 (2 : ZMod 31597729523)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379, 1), (977, 1), (42667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379, 1), (977, 1), (42667, 1)] : List FactorBlock).map factorBlockValue).prod) = 31597729523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_379
      · exact prime_oneHundredFortyFiveEM_977
      · exact prime_oneHundredFortyFiveEM_42667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31597729523) ^ 15798864761 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31597729523) ^ 83371318 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31597729523) ^ 32341586 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 31597729523) ^ 740566 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_33657791521 : Nat.Prime 33657791521 := by
  apply lucas_primality 33657791521 (11 : ZMod 33657791521)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (23, 1), (3048713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (23, 1), (3048713, 1)] : List FactorBlock).map factorBlockValue).prod) = 33657791521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_3048713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33657791521) ^ 16828895760 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 33657791521) ^ 11219263840 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 33657791521) ^ 6731558304 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 33657791521) ^ 1463382240 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 33657791521) ^ 11040 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_43587345661 : Nat.Prime 43587345661 := by
  apply lucas_primality 43587345661 (2 : ZMod 43587345661)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (857, 1), (847673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (857, 1), (847673, 1)] : List FactorBlock).map factorBlockValue).prod) = 43587345661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_857
      · exact prime_oneHundredFortyFiveEM_847673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43587345661) ^ 21793672830 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 43587345661) ^ 14529115220 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 43587345661) ^ 8717469132 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 43587345661) ^ 50860380 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 43587345661) ^ 51420 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_56529077249 : Nat.Prime 56529077249 := by
  apply lucas_primality 56529077249 (3 : ZMod 56529077249)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (7, 1), (19, 1), (415069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (7, 1), (19, 1), (415069, 1)] : List FactorBlock).map factorBlockValue).prod) = 56529077249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_415069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56529077249) ^ 28264538624 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 56529077249) ^ 8075582464 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 56529077249) ^ 2975214592 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 56529077249) ^ 136192 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_57367376279 : Nat.Prime 57367376279 := by
  apply lucas_primality 57367376279 (11 : ZMod 57367376279)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (53, 1), (263, 1), (43783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (53, 1), (263, 1), (43783, 1)] : List FactorBlock).map factorBlockValue).prod) = 57367376279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_47
      · exact prime_oneHundredFortyFiveEM_53
      · exact prime_oneHundredFortyFiveEM_263
      · exact prime_oneHundredFortyFiveEM_43783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 57367376279) ^ 28683688139 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 57367376279) ^ 1220582474 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 57367376279) ^ 1082403326 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 57367376279) ^ 218126906 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 57367376279) ^ 1310266 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_58677187757 : Nat.Prime 58677187757 := by
  apply lucas_primality 58677187757 (2 : ZMod 58677187757)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (121233859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (121233859, 1)] : List FactorBlock).map factorBlockValue).prod) = 58677187757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_121233859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58677187757) ^ 29338593878 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 58677187757) ^ 5334289796 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 58677187757) ^ 484 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_63525801517 : Nat.Prime 63525801517 := by
  apply lucas_primality 63525801517 (2 : ZMod 63525801517)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5293816793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5293816793, 1)] : List FactorBlock).map factorBlockValue).prod) = 63525801517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5293816793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63525801517) ^ 31762900758 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 63525801517) ^ 21175267172 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 63525801517) ^ 12 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_63694869989 : Nat.Prime 63694869989 := by
  apply lucas_primality 63694869989 (2 : ZMod 63694869989)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103, 1), (421, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103, 1), (421, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) = 63694869989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_103
      · exact prime_oneHundredFortyFiveEM_421
      · exact prime_oneHundredFortyFiveEM_367219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63694869989) ^ 31847434994 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 63694869989) ^ 618396796 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 63694869989) ^ 151294228 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 63694869989) ^ 173452 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_79420858801 : Nat.Prime 79420858801 := by
  apply lucas_primality 79420858801 (23 : ZMod 79420858801)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (19, 1), (89, 1), (39139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (19, 1), (89, 1), (39139, 1)] : List FactorBlock).map factorBlockValue).prod) = 79420858801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_89
      · exact prime_oneHundredFortyFiveEM_39139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 79420858801) ^ 39710429400 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 79420858801) ^ 26473619600 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 79420858801) ^ 15884171760 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 79420858801) ^ 4180045200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 79420858801) ^ 892369200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (23 : ZMod 79420858801) ^ 2029200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_86106285841 : Nat.Prime 86106285841 := by
  apply lucas_primality 86106285841 (19 : ZMod 86106285841)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (358776191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (358776191, 1)] : List FactorBlock).map factorBlockValue).prod) = 86106285841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_358776191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 86106285841) ^ 43053142920 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (19 : ZMod 86106285841) ^ 28702095280 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (19 : ZMod 86106285841) ^ 17221257168 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (19 : ZMod 86106285841) ^ 240 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_91440978569 : Nat.Prime 91440978569 := by
  apply lucas_primality 91440978569 (3 : ZMod 91440978569)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (394142149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (394142149, 1)] : List FactorBlock).map factorBlockValue).prod) = 91440978569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_394142149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 91440978569) ^ 45720489284 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 91440978569) ^ 3153137192 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 91440978569) ^ 232 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_93496914227 : Nat.Prime 93496914227 := by
  apply lucas_primality 93496914227 (2 : ZMod 93496914227)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1297, 1), (36043529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1297, 1), (36043529, 1)] : List FactorBlock).map factorBlockValue).prod) = 93496914227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_1297
      · exact prime_oneHundredFortyFiveEM_36043529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93496914227) ^ 46748457113 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 93496914227) ^ 72087058 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 93496914227) ^ 2594 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_105243810493 : Nat.Prime 105243810493 := by
  apply lucas_primality 105243810493 (5 : ZMod 105243810493)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (367, 1), (23897323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (367, 1), (23897323, 1)] : List FactorBlock).map factorBlockValue).prod) = 105243810493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_367
      · exact prime_oneHundredFortyFiveEM_23897323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 105243810493) ^ 52621905246 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 105243810493) ^ 35081270164 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 105243810493) ^ 286767876 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 105243810493) ^ 4404 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_122386673323 : Nat.Prime 122386673323 := by
  apply lucas_primality 122386673323 (3 : ZMod 122386673323)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (101481487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (101481487, 1)] : List FactorBlock).map factorBlockValue).prod) = 122386673323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_67
      · exact prime_oneHundredFortyFiveEM_101481487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 122386673323) ^ 61193336661 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 122386673323) ^ 40795557774 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 122386673323) ^ 1826666766 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 122386673323) ^ 1206 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_853
      · exact prime_oneHundredFortyFiveEM_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_159715977601 : Nat.Prime 159715977601 := by
  apply lucas_primality 159715977601 (14 : ZMod 159715977601)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 2), (16637081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 2), (16637081, 1)] : List FactorBlock).map factorBlockValue).prod) = 159715977601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_16637081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 159715977601) ^ 79857988800 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 159715977601) ^ 53238659200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 159715977601) ^ 31943195520 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (14 : ZMod 159715977601) ^ 9600 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_209576336701 : Nat.Prime 209576336701 := by
  apply lucas_primality 209576336701 (2 : ZMod 209576336701)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (59, 1), (89, 1), (133039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (59, 1), (89, 1), (133039, 1)] : List FactorBlock).map factorBlockValue).prod) = 209576336701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_89
      · exact prime_oneHundredFortyFiveEM_133039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 209576336701) ^ 104788168350 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 209576336701) ^ 69858778900 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 209576336701) ^ 41915267340 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 209576336701) ^ 3552141300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 209576336701) ^ 2354790300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 209576336701) ^ 1575300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_245731852043 : Nat.Prime 245731852043 := by
  apply lucas_primality 245731852043 (2 : ZMod 245731852043)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (73, 1), (719, 1), (137699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (73, 1), (719, 1), (137699, 1)] : List FactorBlock).map factorBlockValue).prod) = 245731852043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_73
      · exact prime_oneHundredFortyFiveEM_719
      · exact prime_oneHundredFortyFiveEM_137699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 245731852043) ^ 122865926021 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 245731852043) ^ 14454814826 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 245731852043) ^ 3366189754 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 245731852043) ^ 341768918 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 245731852043) ^ 1784558 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_254318029613 : Nat.Prime 254318029613 := by
  apply lucas_primality 254318029613 (2 : ZMod 254318029613)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (853, 1), (2570219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (853, 1), (2570219, 1)] : List FactorBlock).map factorBlockValue).prod) = 254318029613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_853
      · exact prime_oneHundredFortyFiveEM_2570219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 254318029613) ^ 127159014806 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 254318029613) ^ 8769587228 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 254318029613) ^ 298145404 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 254318029613) ^ 98948 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_259392040133 : Nat.Prime 259392040133 := by
  apply lucas_primality 259392040133 (2 : ZMod 259392040133)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (349, 1), (523, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (349, 1), (523, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) = 259392040133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_349
      · exact prime_oneHundredFortyFiveEM_523
      · exact prime_oneHundredFortyFiveEM_12251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259392040133) ^ 129696020066 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259392040133) ^ 8944553108 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259392040133) ^ 743243668 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259392040133) ^ 495969484 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 259392040133) ^ 21173132 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_288732631151 : Nat.Prime 288732631151 := by
  apply lucas_primality 288732631151 (29 : ZMod 288732631151)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (757, 1), (7628339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (757, 1), (7628339, 1)] : List FactorBlock).map factorBlockValue).prod) = 288732631151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_757
      · exact prime_oneHundredFortyFiveEM_7628339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 288732631151) ^ 144366315575 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 288732631151) ^ 57746526230 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 288732631151) ^ 381416950 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 288732631151) ^ 37850 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_303164107717 : Nat.Prime 303164107717 := by
  apply lucas_primality 303164107717 (2 : ZMod 303164107717)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (132421, 1), (190783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (132421, 1), (190783, 1)] : List FactorBlock).map factorBlockValue).prod) = 303164107717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_132421
      · exact prime_oneHundredFortyFiveEM_190783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 303164107717) ^ 151582053858 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 303164107717) ^ 101054702572 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 303164107717) ^ 2289396 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 303164107717) ^ 1589052 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_323121618121 : Nat.Prime 323121618121 := by
  apply lucas_primality 323121618121 (38 : ZMod 323121618121)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (384668593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (384668593, 1)] : List FactorBlock).map factorBlockValue).prod) = 323121618121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_384668593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 323121618121) ^ 161560809060 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (38 : ZMod 323121618121) ^ 107707206040 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (38 : ZMod 323121618121) ^ 64624323624 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (38 : ZMod 323121618121) ^ 46160231160 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (38 : ZMod 323121618121) ^ 840 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_419378708389 : Nat.Prime 419378708389 := by
  apply lucas_primality 419378708389 (2 : ZMod 419378708389)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (5323, 1), (226397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (5323, 1), (226397, 1)] : List FactorBlock).map factorBlockValue).prod) = 419378708389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_5323
      · exact prime_oneHundredFortyFiveEM_226397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 419378708389) ^ 209689354194 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 419378708389) ^ 139792902796 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 419378708389) ^ 14461334772 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 419378708389) ^ 78786156 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 419378708389) ^ 1852404 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_508636059227 : Nat.Prime 508636059227 := by
  apply lucas_primality 508636059227 (2 : ZMod 508636059227)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (254318029613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (254318029613, 1)] : List FactorBlock).map factorBlockValue).prod) = 508636059227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_254318029613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 508636059227) ^ 254318029613 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 508636059227) ^ 2 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_572646669631 : Nat.Prime 572646669631 := by
  apply lucas_primality 572646669631 (6 : ZMod 572646669631)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (43, 1), (239, 1), (265339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (43, 1), (239, 1), (265339, 1)] : List FactorBlock).map factorBlockValue).prod) = 572646669631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_43
      · exact prime_oneHundredFortyFiveEM_239
      · exact prime_oneHundredFortyFiveEM_265339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 572646669631) ^ 286323334815 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 190882223210 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 114529333926 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 81806667090 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 13317364410 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 2396011170 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 572646669631) ^ 2158170 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_634236766099 : Nat.Prime 634236766099 := by
  apply lucas_primality 634236766099 (3 : ZMod 634236766099)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (18517, 1), (439123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (18517, 1), (439123, 1)] : List FactorBlock).map factorBlockValue).prod) = 634236766099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_18517
      · exact prime_oneHundredFortyFiveEM_439123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 634236766099) ^ 317118383049 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 634236766099) ^ 211412255366 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 634236766099) ^ 48787443546 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 634236766099) ^ 34251594 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 634236766099) ^ 1444326 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_765392109809 : Nat.Prime 765392109809 := by
  apply lucas_primality 765392109809 (3 : ZMod 765392109809)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (190591, 1), (250993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (190591, 1), (250993, 1)] : List FactorBlock).map factorBlockValue).prod) = 765392109809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_190591
      · exact prime_oneHundredFortyFiveEM_250993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 765392109809) ^ 382696054904 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 765392109809) ^ 4015888 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 765392109809) ^ 3049456 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_898195460401 : Nat.Prime 898195460401 := by
  apply lucas_primality 898195460401 (11 : ZMod 898195460401)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 2), (127, 1), (40093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 2), (127, 1), (40093, 1)] : List FactorBlock).map factorBlockValue).prod) = 898195460401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_127
      · exact prime_oneHundredFortyFiveEM_40093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 898195460401) ^ 449097730200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 898195460401) ^ 299398486800 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 898195460401) ^ 179639092080 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 898195460401) ^ 128313637200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 898195460401) ^ 7072405200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 898195460401) ^ 22402800 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_982491534593 : Nat.Prime 982491534593 := by
  apply lucas_primality 982491534593 (3 : ZMod 982491534593)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (19, 1), (487, 1), (414769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (19, 1), (487, 1), (414769, 1)] : List FactorBlock).map factorBlockValue).prod) = 982491534593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_487
      · exact prime_oneHundredFortyFiveEM_414769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 982491534593) ^ 491245767296 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 982491534593) ^ 51710080768 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 982491534593) ^ 2017436416 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 982491534593) ^ 2368768 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_983462925481 : Nat.Prime 983462925481 := by
  apply lucas_primality 983462925481 (31 : ZMod 983462925481)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (16249, 1), (72053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (16249, 1), (72053, 1)] : List FactorBlock).map factorBlockValue).prod) = 983462925481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_16249
      · exact prime_oneHundredFortyFiveEM_72053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 983462925481) ^ 491731462740 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (31 : ZMod 983462925481) ^ 327820975160 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (31 : ZMod 983462925481) ^ 196692585096 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (31 : ZMod 983462925481) ^ 140494703640 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (31 : ZMod 983462925481) ^ 60524520 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (31 : ZMod 983462925481) ^ 13649160 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1179825150919 : Nat.Prime 1179825150919 := by
  apply lucas_primality 1179825150919 (6 : ZMod 1179825150919)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2347, 1), (83782499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2347, 1), (83782499, 1)] : List FactorBlock).map factorBlockValue).prod) = 1179825150919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_2347
      · exact prime_oneHundredFortyFiveEM_83782499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1179825150919) ^ 589912575459 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1179825150919) ^ 393275050306 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1179825150919) ^ 502694994 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1179825150919) ^ 14082 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1390510820353 : Nat.Prime 1390510820353 := by
  apply lucas_primality 1390510820353 (5 : ZMod 1390510820353)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (661, 1), (691, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (661, 1), (691, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod) = 1390510820353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_661
      · exact prime_oneHundredFortyFiveEM_691
      · exact prime_oneHundredFortyFiveEM_991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1390510820353) ^ 695255410176 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1390510820353) ^ 463503606784 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1390510820353) ^ 2103647232 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1390510820353) ^ 2012316672 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1390510820353) ^ 1403139072 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1469067598847 : Nat.Prime 1469067598847 := by
  apply lucas_primality 1469067598847 (5 : ZMod 1469067598847)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (599, 1), (23137109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (599, 1), (23137109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1469067598847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_53
      · exact prime_oneHundredFortyFiveEM_599
      · exact prime_oneHundredFortyFiveEM_23137109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1469067598847) ^ 734533799423 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1469067598847) ^ 27718256582 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1469067598847) ^ 2452533554 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1469067598847) ^ 63494 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1496564045849 : Nat.Prime 1496564045849 := by
  apply lucas_primality 1496564045849 (3 : ZMod 1496564045849)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (233, 1), (4003, 1), (200569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (233, 1), (4003, 1), (200569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1496564045849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_233
      · exact prime_oneHundredFortyFiveEM_4003
      · exact prime_oneHundredFortyFiveEM_200569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1496564045849) ^ 748282022924 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1496564045849) ^ 6423021656 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1496564045849) ^ 373860616 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1496564045849) ^ 7461592 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1964983069187 : Nat.Prime 1964983069187 := by
  apply lucas_primality 1964983069187 (2 : ZMod 1964983069187)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (982491534593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (982491534593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1964983069187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_982491534593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1964983069187) ^ 982491534593 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1964983069187) ^ 2 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1977966871619 : Nat.Prime 1977966871619 := by
  apply lucas_primality 1977966871619 (2 : ZMod 1977966871619)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3191, 1), (309928999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3191, 1), (309928999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1977966871619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3191
      · exact prime_oneHundredFortyFiveEM_309928999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1977966871619) ^ 988983435809 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1977966871619) ^ 619857998 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1977966871619) ^ 6382 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2258914624817 : Nat.Prime 2258914624817 := by
  apply lucas_primality 2258914624817 (3 : ZMod 2258914624817)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (313, 1), (451061227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (313, 1), (451061227, 1)] : List FactorBlock).map factorBlockValue).prod) = 2258914624817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_313
      · exact prime_oneHundredFortyFiveEM_451061227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2258914624817) ^ 1129457312408 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2258914624817) ^ 7216979632 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2258914624817) ^ 5008 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2620750481123 : Nat.Prime 2620750481123 := by
  apply lucas_primality 2620750481123 (2 : ZMod 2620750481123)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (271, 1), (117934951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (271, 1), (117934951, 1)] : List FactorBlock).map factorBlockValue).prod) = 2620750481123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_41
      · exact prime_oneHundredFortyFiveEM_271
      · exact prime_oneHundredFortyFiveEM_117934951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2620750481123) ^ 1310375240561 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2620750481123) ^ 63920743442 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2620750481123) ^ 9670665982 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2620750481123) ^ 22222 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2772657679301 : Nat.Prime 2772657679301 := by
  apply lucas_primality 2772657679301 (2 : ZMod 2772657679301)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (751, 1), (1190953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (751, 1), (1190953, 1)] : List FactorBlock).map factorBlockValue).prod) = 2772657679301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_31
      · exact prime_oneHundredFortyFiveEM_751
      · exact prime_oneHundredFortyFiveEM_1190953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2772657679301) ^ 1386328839650 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2772657679301) ^ 554531535860 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2772657679301) ^ 89440570300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2772657679301) ^ 3691954300 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2772657679301) ^ 2328100 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_3311184798931 : Nat.Prime 3311184798931 := by
  apply lucas_primality 3311184798931 (7 : ZMod 3311184798931)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (293, 1), (12989623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (293, 1), (12989623, 1)] : List FactorBlock).map factorBlockValue).prod) = 3311184798931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_293
      · exact prime_oneHundredFortyFiveEM_12989623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3311184798931) ^ 1655592399465 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3311184798931) ^ 1103728266310 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3311184798931) ^ 662236959786 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3311184798931) ^ 114178786170 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3311184798931) ^ 11300972010 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3311184798931) ^ 254910 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_3317730120431 : Nat.Prime 3317730120431 := by
  apply lucas_primality 3317730120431 (11 : ZMod 3317730120431)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (167249, 1), (180337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (167249, 1), (180337, 1)] : List FactorBlock).map factorBlockValue).prod) = 3317730120431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_167249
      · exact prime_oneHundredFortyFiveEM_180337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3317730120431) ^ 1658865060215 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 3317730120431) ^ 663546024086 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 3317730120431) ^ 301611829130 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 3317730120431) ^ 19837070 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 3317730120431) ^ 18397390 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_4369146618673 : Nat.Prime 4369146618673 := by
  apply lucas_primality 4369146618673 (5 : ZMod 4369146618673)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 1), (23, 2), (579353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 1), (23, 2), (579353, 1)] : List FactorBlock).map factorBlockValue).prod) = 4369146618673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_579353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4369146618673) ^ 2184573309336 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4369146618673) ^ 1456382206224 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4369146618673) ^ 397195147152 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4369146618673) ^ 189962896464 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 4369146618673) ^ 7541424 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_5182580268527 : Nat.Prime 5182580268527 := by
  apply lucas_primality 5182580268527 (5 : ZMod 5182580268527)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (101, 1), (179, 1), (7543763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (101, 1), (179, 1), (7543763, 1)] : List FactorBlock).map factorBlockValue).prod) = 5182580268527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_101
      · exact prime_oneHundredFortyFiveEM_179
      · exact prime_oneHundredFortyFiveEM_7543763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5182580268527) ^ 2591290134263 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5182580268527) ^ 272767382554 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5182580268527) ^ 51312675926 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5182580268527) ^ 28952962394 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 5182580268527) ^ 687002 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_11277761949743 : Nat.Prime 11277761949743 := by
  apply lucas_primality 11277761949743 (5 : ZMod 11277761949743)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (79420858801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (79420858801, 1)] : List FactorBlock).map factorBlockValue).prod) = 11277761949743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_71
      · exact prime_oneHundredFortyFiveEM_79420858801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11277761949743) ^ 5638880974871 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11277761949743) ^ 158841717602 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11277761949743) ^ 142 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_11773398390263 : Nat.Prime 11773398390263 := by
  apply lucas_primality 11773398390263 (5 : ZMod 11773398390263)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1193, 1), (290256851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1193, 1), (290256851, 1)] : List FactorBlock).map factorBlockValue).prod) = 11773398390263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_1193
      · exact prime_oneHundredFortyFiveEM_290256851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11773398390263) ^ 5886699195131 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11773398390263) ^ 692552846486 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11773398390263) ^ 9868732934 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 11773398390263) ^ 40562 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_11795706684821 : Nat.Prime 11795706684821 := by
  apply lucas_primality 11795706684821 (2 : ZMod 11795706684821)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (34327, 1), (17181383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (34327, 1), (17181383, 1)] : List FactorBlock).map factorBlockValue).prod) = 11795706684821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_34327
      · exact prime_oneHundredFortyFiveEM_17181383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11795706684821) ^ 5897853342410 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11795706684821) ^ 2359141336964 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11795706684821) ^ 343627660 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11795706684821) ^ 686540 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_12103373607107 : Nat.Prime 12103373607107 := by
  apply lucas_primality 12103373607107 (2 : ZMod 12103373607107)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (811, 1), (7462005923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (811, 1), (7462005923, 1)] : List FactorBlock).map factorBlockValue).prod) = 12103373607107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_811
      · exact prime_oneHundredFortyFiveEM_7462005923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12103373607107) ^ 6051686803553 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12103373607107) ^ 14924011846 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12103373607107) ^ 1622 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_12567283235797 : Nat.Prime 12567283235797 := by
  apply lucas_primality 12567283235797 (2 : ZMod 12567283235797)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (113, 1), (9267907991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (113, 1), (9267907991, 1)] : List FactorBlock).map factorBlockValue).prod) = 12567283235797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_113
      · exact prime_oneHundredFortyFiveEM_9267907991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12567283235797) ^ 6283641617898 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12567283235797) ^ 4189094411932 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12567283235797) ^ 111214895892 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12567283235797) ^ 1356 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_13408669673461 : Nat.Prime 13408669673461 := by
  apply lucas_primality 13408669673461 (6 : ZMod 13408669673461)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (907, 1), (82130771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (907, 1), (82130771, 1)] : List FactorBlock).map factorBlockValue).prod) = 13408669673461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_907
      · exact prime_oneHundredFortyFiveEM_82130771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13408669673461) ^ 6704334836730 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 13408669673461) ^ 4469556557820 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 13408669673461) ^ 2681733934692 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 13408669673461) ^ 14783538780 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 13408669673461) ^ 163260 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_14194771174511 : Nat.Prime 14194771174511 := by
  apply lucas_primality 14194771174511 (7 : ZMod 14194771174511)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11681, 1), (121520171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11681, 1), (121520171, 1)] : List FactorBlock).map factorBlockValue).prod) = 14194771174511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_11681
      · exact prime_oneHundredFortyFiveEM_121520171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14194771174511) ^ 7097385587255 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 14194771174511) ^ 2838954234902 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 14194771174511) ^ 1215201710 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 14194771174511) ^ 116810 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_14798442555431 : Nat.Prime 14798442555431 := by
  apply lucas_primality 14798442555431 (13 : ZMod 14798442555431)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (598981, 1), (2470603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (598981, 1), (2470603, 1)] : List FactorBlock).map factorBlockValue).prod) = 14798442555431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_598981
      · exact prime_oneHundredFortyFiveEM_2470603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 14798442555431) ^ 7399221277715 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14798442555431) ^ 2959688511086 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14798442555431) ^ 24706030 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (13 : ZMod 14798442555431) ^ 5989810 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_14802789757447 : Nat.Prime 14802789757447 := by
  apply lucas_primality 14802789757447 (3 : ZMod 14802789757447)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (503, 1), (544981583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (503, 1), (544981583, 1)] : List FactorBlock).map factorBlockValue).prod) = 14802789757447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_503
      · exact prime_oneHundredFortyFiveEM_544981583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14802789757447) ^ 7401394878723 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14802789757447) ^ 4934263252482 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14802789757447) ^ 29429005482 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 14802789757447) ^ 27162 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_19347880098749 : Nat.Prime 19347880098749 := by
  apply lucas_primality 19347880098749 (2 : ZMod 19347880098749)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (2447, 1), (116276113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (2447, 1), (116276113, 1)] : List FactorBlock).map factorBlockValue).prod) = 19347880098749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_2447
      · exact prime_oneHundredFortyFiveEM_116276113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19347880098749) ^ 9673940049374 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 19347880098749) ^ 1138110594044 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 19347880098749) ^ 7906775684 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 19347880098749) ^ 166396 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_20129035334069 : Nat.Prime 20129035334069 := by
  apply lucas_primality 20129035334069 (2 : ZMod 20129035334069)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (29, 1), (79613, 1), (128213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (29, 1), (79613, 1), (128213, 1)] : List FactorBlock).map factorBlockValue).prod) = 20129035334069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_79613
      · exact prime_oneHundredFortyFiveEM_128213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20129035334069) ^ 10064517667034 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20129035334069) ^ 1184060902004 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20129035334069) ^ 694104666692 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20129035334069) ^ 252836036 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20129035334069) ^ 156996836 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_27824990649587 : Nat.Prime 27824990649587 := by
  apply lucas_primality 27824990649587 (2 : ZMod 27824990649587)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (503, 1), (125154011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (503, 1), (125154011, 1)] : List FactorBlock).map factorBlockValue).prod) = 27824990649587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_503
      · exact prime_oneHundredFortyFiveEM_125154011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27824990649587) ^ 13912495324793 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27824990649587) ^ 2140383896122 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27824990649587) ^ 1636764155858 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27824990649587) ^ 55318072862 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27824990649587) ^ 222326 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_45039781034081 : Nat.Prime 45039781034081 := by
  apply lucas_primality 45039781034081 (6 : ZMod 45039781034081)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (101, 1), (398159309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (101, 1), (398159309, 1)] : List FactorBlock).map factorBlockValue).prod) = 45039781034081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_101
      · exact prime_oneHundredFortyFiveEM_398159309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45039781034081) ^ 22519890517040 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 45039781034081) ^ 9007956206816 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 45039781034081) ^ 6434254433440 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 45039781034081) ^ 445938426080 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 45039781034081) ^ 113120 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_48392211162989 : Nat.Prime 48392211162989 := by
  apply lucas_primality 48392211162989 (2 : ZMod 48392211162989)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (11909, 1), (13193179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (11909, 1), (13193179, 1)] : List FactorBlock).map factorBlockValue).prod) = 48392211162989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_11909
      · exact prime_oneHundredFortyFiveEM_13193179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48392211162989) ^ 24196105581494 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 48392211162989) ^ 6913173023284 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 48392211162989) ^ 4399291923908 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 48392211162989) ^ 4063499132 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 48392211162989) ^ 3667972 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_57271534030589 : Nat.Prime 57271534030589 := by
  apply lucas_primality 57271534030589 (2 : ZMod 57271534030589)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (19973, 1), (19374647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (19973, 1), (19374647, 1)] : List FactorBlock).map factorBlockValue).prod) = 57271534030589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_37
      · exact prime_oneHundredFortyFiveEM_19973
      · exact prime_oneHundredFortyFiveEM_19374647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57271534030589) ^ 28635767015294 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57271534030589) ^ 1547879298124 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57271534030589) ^ 2867447756 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 57271534030589) ^ 2956004 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_61020001436509 : Nat.Prime 61020001436509 := by
  apply lucas_primality 61020001436509 (2 : ZMod 61020001436509)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (270407, 1), (696481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (270407, 1), (696481, 1)] : List FactorBlock).map factorBlockValue).prod) = 61020001436509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_270407
      · exact prime_oneHundredFortyFiveEM_696481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61020001436509) ^ 30510000718254 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61020001436509) ^ 20340000478836 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61020001436509) ^ 225659844 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 61020001436509) ^ 87611868 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_83312889945613 : Nat.Prime 83312889945613 := by
  apply lucas_primality 83312889945613 (2 : ZMod 83312889945613)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (63694869989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (63694869989, 1)] : List FactorBlock).map factorBlockValue).prod) = 83312889945613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_109
      · exact prime_oneHundredFortyFiveEM_63694869989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83312889945613) ^ 41656444972806 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83312889945613) ^ 27770963315204 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83312889945613) ^ 764338439868 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83312889945613) ^ 1308 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_173
      · exact prime_oneHundredFortyFiveEM_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_120560370588107 : Nat.Prime 120560370588107 := by
  apply lucas_primality 120560370588107 (2 : ZMod 120560370588107)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6067, 1), (9935748359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6067, 1), (9935748359, 1)] : List FactorBlock).map factorBlockValue).prod) = 120560370588107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_6067
      · exact prime_oneHundredFortyFiveEM_9935748359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120560370588107) ^ 60280185294053 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 120560370588107) ^ 19871496718 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 120560370588107) ^ 12134 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_173007358726229 : Nat.Prime 173007358726229 := by
  apply lucas_primality 173007358726229 (2 : ZMod 173007358726229)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (17, 1), (10939, 1), (1376231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (17, 1), (10939, 1), (1376231, 1)] : List FactorBlock).map factorBlockValue).prod) = 173007358726229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_10939
      · exact prime_oneHundredFortyFiveEM_1376231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 173007358726229) ^ 86503679363114 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 173007358726229) ^ 13308258363556 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 173007358726229) ^ 10176903454484 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 173007358726229) ^ 15815646652 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 173007358726229) ^ 125710988 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_174925715176777 : Nat.Prime 174925715176777 := by
  apply lucas_primality 174925715176777 (5 : ZMod 174925715176777)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (1439, 1), (4591, 1), (25657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (1439, 1), (4591, 1), (25657, 1)] : List FactorBlock).map factorBlockValue).prod) = 174925715176777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_43
      · exact prime_oneHundredFortyFiveEM_1439
      · exact prime_oneHundredFortyFiveEM_4591
      · exact prime_oneHundredFortyFiveEM_25657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 174925715176777) ^ 87462857588388 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 174925715176777) ^ 58308571725592 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 174925715176777) ^ 4068039887832 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 174925715176777) ^ 121560608184 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 174925715176777) ^ 38101876536 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 174925715176777) ^ 6817855368 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_272608044935537 : Nat.Prime 272608044935537 := by
  apply lucas_primality 272608044935537 (3 : ZMod 272608044935537)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (131, 1), (167, 1), (14717, 1), (52919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (131, 1), (167, 1), (14717, 1), (52919, 1)] : List FactorBlock).map factorBlockValue).prod) = 272608044935537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_131
      · exact prime_oneHundredFortyFiveEM_167
      · exact prime_oneHundredFortyFiveEM_14717
      · exact prime_oneHundredFortyFiveEM_52919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 272608044935537) ^ 136304022467768 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 272608044935537) ^ 2080977442256 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 272608044935537) ^ 1632383502608 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 272608044935537) ^ 18523343408 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 272608044935537) ^ 5151420944 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_290904508172549 : Nat.Prime 290904508172549 := by
  apply lucas_primality 290904508172549 (2 : ZMod 290904508172549)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (572646669631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (572646669631, 1)] : List FactorBlock).map factorBlockValue).prod) = 290904508172549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_127
      · exact prime_oneHundredFortyFiveEM_572646669631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 290904508172549) ^ 145452254086274 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 290904508172549) ^ 2290586678524 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 290904508172549) ^ 508 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_313617806795011 : Nat.Prime 313617806795011 := by
  apply lucas_primality 313617806795011 (2 : ZMod 313617806795011)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (677, 1), (2153, 1), (7172107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (677, 1), (2153, 1), (7172107, 1)] : List FactorBlock).map factorBlockValue).prod) = 313617806795011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_677
      · exact prime_oneHundredFortyFiveEM_2153
      · exact prime_oneHundredFortyFiveEM_7172107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 313617806795011) ^ 156808903397505 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 313617806795011) ^ 104539268931670 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 313617806795011) ^ 62723561359002 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 313617806795011) ^ 463246391130 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 313617806795011) ^ 145665493170 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 313617806795011) ^ 43727430 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_316877884485823 : Nat.Prime 316877884485823 := by
  apply lucas_primality 316877884485823 (3 : ZMod 316877884485823)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1453, 1), (1101440713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1453, 1), (1101440713, 1)] : List FactorBlock).map factorBlockValue).prod) = 316877884485823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_1453
      · exact prime_oneHundredFortyFiveEM_1101440713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 316877884485823) ^ 158438942242911 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 316877884485823) ^ 105625961495274 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 316877884485823) ^ 28807080407802 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 316877884485823) ^ 218085261174 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 316877884485823) ^ 287694 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_327674783079929 : Nat.Prime 327674783079929 := by
  apply lucas_primality 327674783079929 (3 : ZMod 327674783079929)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (66587, 1), (21211217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (66587, 1), (21211217, 1)] : List FactorBlock).map factorBlockValue).prod) = 327674783079929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_66587
      · exact prime_oneHundredFortyFiveEM_21211217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 327674783079929) ^ 163837391539964 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 327674783079929) ^ 11299130451032 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 327674783079929) ^ 4921002344 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 327674783079929) ^ 15448184 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_346044176929453 : Nat.Prime 346044176929453 := by
  apply lucas_primality 346044176929453 (5 : ZMod 346044176929453)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7687, 1), (3751400383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7687, 1), (3751400383, 1)] : List FactorBlock).map factorBlockValue).prod) = 346044176929453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7687
      · exact prime_oneHundredFortyFiveEM_3751400383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 346044176929453) ^ 173022088464726 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 346044176929453) ^ 115348058976484 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 346044176929453) ^ 45016804596 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 346044176929453) ^ 92244 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_409124106445289 : Nat.Prime 409124106445289 := by
  apply lucas_primality 409124106445289 (3 : ZMod 409124106445289)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (23, 1), (41, 1), (4171670879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (23, 1), (41, 1), (4171670879, 1)] : List FactorBlock).map factorBlockValue).prod) = 409124106445289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_41
      · exact prime_oneHundredFortyFiveEM_4171670879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 409124106445289) ^ 204562053222644 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 409124106445289) ^ 31471085111176 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 409124106445289) ^ 17788004628056 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 409124106445289) ^ 9978636742568 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 409124106445289) ^ 98072 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_630426284576651 : Nat.Prime 630426284576651 := by
  apply lucas_primality 630426284576651 (2 : ZMod 630426284576651)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (53, 1), (73, 1), (3258859057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (53, 1), (73, 1), (3258859057, 1)] : List FactorBlock).map factorBlockValue).prod) = 630426284576651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_53
      · exact prime_oneHundredFortyFiveEM_73
      · exact prime_oneHundredFortyFiveEM_3258859057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 630426284576651) ^ 315213142288325 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 630426284576651) ^ 126085256915330 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 630426284576651) ^ 11894835558050 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 630426284576651) ^ 8635976501050 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 630426284576651) ^ 193450 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_702346337918723 : Nat.Prime 702346337918723 := by
  apply lucas_primality 702346337918723 (2 : ZMod 702346337918723)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (67, 1), (21347, 1), (1525049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (67, 1), (21347, 1), (1525049, 1)] : List FactorBlock).map factorBlockValue).prod) = 702346337918723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_67
      · exact prime_oneHundredFortyFiveEM_21347
      · exact prime_oneHundredFortyFiveEM_1525049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 702346337918723) ^ 351173168959361 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 702346337918723) ^ 100335191131246 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 702346337918723) ^ 30536797300814 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 702346337918723) ^ 10482781162966 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 702346337918723) ^ 32901407126 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 702346337918723) ^ 460540178 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_854693807696783 : Nat.Prime 854693807696783 := by
  apply lucas_primality 854693807696783 (5 : ZMod 854693807696783)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1019, 1), (419378708389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1019, 1), (419378708389, 1)] : List FactorBlock).map factorBlockValue).prod) = 854693807696783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_1019
      · exact prime_oneHundredFortyFiveEM_419378708389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 854693807696783) ^ 427346903848391 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 854693807696783) ^ 838757416778 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 854693807696783) ^ 2038 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_889812056760593 : Nat.Prime 889812056760593 := by
  apply lucas_primality 889812056760593 (3 : ZMod 889812056760593)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (67, 1), (7451, 1), (2273489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (67, 1), (7451, 1), (2273489, 1)] : List FactorBlock).map factorBlockValue).prod) = 889812056760593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_67
      · exact prime_oneHundredFortyFiveEM_7451
      · exact prime_oneHundredFortyFiveEM_2273489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 889812056760593) ^ 444906028380296 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 889812056760593) ^ 127116008108656 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 889812056760593) ^ 13280776966576 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 889812056760593) ^ 119421830192 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 889812056760593) ^ 391386128 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1089894365833439 : Nat.Prime 1089894365833439 := by
  apply lucas_primality 1089894365833439 (11 : ZMod 1089894365833439)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (6653, 1), (68351, 1), (108943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (6653, 1), (68351, 1), (108943, 1)] : List FactorBlock).map factorBlockValue).prod) = 1089894365833439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_6653
      · exact prime_oneHundredFortyFiveEM_68351
      · exact prime_oneHundredFortyFiveEM_108943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1089894365833439) ^ 544947182916719 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1089894365833439) ^ 99081305984858 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1089894365833439) ^ 163819985846 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1089894365833439) ^ 15945551138 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 1089894365833439) ^ 10004262466 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1562538800350469 : Nat.Prime 1562538800350469 := by
  apply lucas_primality 1562538800350469 (2 : ZMod 1562538800350469)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (53, 1), (35801, 1), (10835431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (53, 1), (35801, 1), (10835431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1562538800350469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_53
      · exact prime_oneHundredFortyFiveEM_35801
      · exact prime_oneHundredFortyFiveEM_10835431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1562538800350469) ^ 781269400175234 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1562538800350469) ^ 82238884228972 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1562538800350469) ^ 29481864157556 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1562538800350469) ^ 43645116068 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1562538800350469) ^ 144206428 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1569032607879019 : Nat.Prime 1569032607879019 := by
  apply lucas_primality 1569032607879019 (10 : ZMod 1569032607879019)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (53, 1), (10321, 1), (17705953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (53, 1), (10321, 1), (17705953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1569032607879019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_53
      · exact prime_oneHundredFortyFiveEM_10321
      · exact prime_oneHundredFortyFiveEM_17705953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1569032607879019) ^ 784516303939509 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1569032607879019) ^ 523010869293006 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1569032607879019) ^ 29604388827906 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1569032607879019) ^ 152023312458 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1569032607879019) ^ 88616106 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1779624113521187 : Nat.Prime 1779624113521187 := by
  apply lucas_primality 1779624113521187 (2 : ZMod 1779624113521187)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (889812056760593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (889812056760593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1779624113521187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_889812056760593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1779624113521187) ^ 889812056760593 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1779624113521187) ^ 2 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1819282674810437 : Nat.Prime 1819282674810437 := by
  apply lucas_primality 1819282674810437 (2 : ZMod 1819282674810437)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (373, 1), (9887, 1), (11211769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (373, 1), (9887, 1), (11211769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1819282674810437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_373
      · exact prime_oneHundredFortyFiveEM_9887
      · exact prime_oneHundredFortyFiveEM_11211769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1819282674810437) ^ 909641337405218 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819282674810437) ^ 165389334073676 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819282674810437) ^ 4877433444532 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819282674810437) ^ 184007552828 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1819282674810437) ^ 162265444 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_3792285681927037 : Nat.Prime 3792285681927037 := by
  apply lucas_primality 3792285681927037 (2 : ZMod 3792285681927037)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (625199, 1), (72211021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (625199, 1), (72211021, 1)] : List FactorBlock).map factorBlockValue).prod) = 3792285681927037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_625199
      · exact prime_oneHundredFortyFiveEM_72211021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3792285681927037) ^ 1896142840963518 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3792285681927037) ^ 1264095227309012 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3792285681927037) ^ 541755097418148 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3792285681927037) ^ 6065725764 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3792285681927037) ^ 52516716 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_4206397224699179 : Nat.Prime 4206397224699179 := by
  apply lucas_primality 4206397224699179 (2 : ZMod 4206397224699179)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (283, 1), (323121618121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (283, 1), (323121618121, 1)] : List FactorBlock).map factorBlockValue).prod) = 4206397224699179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_283
      · exact prime_oneHundredFortyFiveEM_323121618121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4206397224699179) ^ 2103198612349589 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4206397224699179) ^ 182886835856486 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4206397224699179) ^ 14863594433566 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4206397224699179) ^ 13018 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_5515390961148161 : Nat.Prime 5515390961148161 := by
  apply lucas_primality 5515390961148161 (6 : ZMod 5515390961148161)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (17, 2), (14909685773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (17, 2), (14909685773, 1)] : List FactorBlock).map factorBlockValue).prod) = 5515390961148161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_14909685773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5515390961148161) ^ 2757695480574080 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 5515390961148161) ^ 1103078192229632 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 5515390961148161) ^ 324434762420480 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 5515390961148161) ^ 369920 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_5949602148268997 : Nat.Prime 5949602148268997 := by
  apply lucas_primality 5949602148268997 (2 : ZMod 5949602148268997)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (5182580268527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (5182580268527, 1)] : List FactorBlock).map factorBlockValue).prod) = 5949602148268997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_41
      · exact prime_oneHundredFortyFiveEM_5182580268527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5949602148268997) ^ 2974801074134498 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5949602148268997) ^ 849943164038428 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5949602148268997) ^ 145112247518756 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5949602148268997) ^ 1148 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_6020057603059879 : Nat.Prime 6020057603059879 := by
  apply lucas_primality 6020057603059879 (6 : ZMod 6020057603059879)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (587, 1), (20521, 1), (11899117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (587, 1), (20521, 1), (11899117, 1)] : List FactorBlock).map factorBlockValue).prod) = 6020057603059879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_587
      · exact prime_oneHundredFortyFiveEM_20521
      · exact prime_oneHundredFortyFiveEM_11899117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6020057603059879) ^ 3010028801529939 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6020057603059879) ^ 2006685867686626 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6020057603059879) ^ 860008229008554 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6020057603059879) ^ 10255634758194 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6020057603059879) ^ 293360830518 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6020057603059879) ^ 505924734 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_6272544950999753 : Nat.Prime 6272544950999753 := by
  apply lucas_primality 6272544950999753 (3 : ZMod 6272544950999753)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14747, 1), (110753, 1), (480059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14747, 1), (110753, 1), (480059, 1)] : List FactorBlock).map factorBlockValue).prod) = 6272544950999753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_14747
      · exact prime_oneHundredFortyFiveEM_110753
      · exact prime_oneHundredFortyFiveEM_480059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6272544950999753) ^ 3136272475499876 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6272544950999753) ^ 425343795416 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6272544950999753) ^ 56635440584 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6272544950999753) ^ 13066195928 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_6849149554957147 : Nat.Prime 6849149554957147 := by
  apply lucas_primality 6849149554957147 (2 : ZMod 6849149554957147)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (19347880098749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (19347880098749, 1)] : List FactorBlock).map factorBlockValue).prod) = 6849149554957147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_19347880098749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6849149554957147) ^ 3424574777478573 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6849149554957147) ^ 2283049851652382 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6849149554957147) ^ 116087280592494 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6849149554957147) ^ 354 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_6859835481253493 : Nat.Prime 6859835481253493 := by
  apply lucas_primality 6859835481253493 (2 : ZMod 6859835481253493)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (277, 1), (193951, 1), (31921399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (277, 1), (193951, 1), (31921399, 1)] : List FactorBlock).map factorBlockValue).prod) = 6859835481253493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_277
      · exact prime_oneHundredFortyFiveEM_193951
      · exact prime_oneHundredFortyFiveEM_31921399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6859835481253493) ^ 3429917740626746 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6859835481253493) ^ 24764749029796 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6859835481253493) ^ 35368910092 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6859835481253493) ^ 214897708 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_8157968482423127 : Nat.Prime 8157968482423127 := by
  apply lucas_primality 8157968482423127 (5 : ZMod 8157968482423127)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19463, 1), (209576336701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19463, 1), (209576336701, 1)] : List FactorBlock).map factorBlockValue).prod) = 8157968482423127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_19463
      · exact prime_oneHundredFortyFiveEM_209576336701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8157968482423127) ^ 4078984241211563 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 8157968482423127) ^ 419152673402 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 8157968482423127) ^ 38926 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_9889213193728541 : Nat.Prime 9889213193728541 := by
  apply lucas_primality 9889213193728541 (12 : ZMod 9889213193728541)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (233, 1), (303164107717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (233, 1), (303164107717, 1)] : List FactorBlock).map factorBlockValue).prod) = 9889213193728541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_233
      · exact prime_oneHundredFortyFiveEM_303164107717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 9889213193728541) ^ 4944606596864270 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 9889213193728541) ^ 1977842638745708 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 9889213193728541) ^ 1412744741961220 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 9889213193728541) ^ 42442975080380 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 9889213193728541) ^ 32620 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_11994594132657967 : Nat.Prime 11994594132657967 := by
  apply lucas_primality 11994594132657967 (3 : ZMod 11994594132657967)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (941609, 1), (2123067029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (941609, 1), (2123067029, 1)] : List FactorBlock).map factorBlockValue).prod) = 11994594132657967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_941609
      · exact prime_oneHundredFortyFiveEM_2123067029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11994594132657967) ^ 5997297066328983 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 11994594132657967) ^ 3998198044219322 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 11994594132657967) ^ 12738402174 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 11994594132657967) ^ 5649654 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_12457590369460309 : Nat.Prime 12457590369460309 := by
  apply lucas_primality 12457590369460309 (6 : ZMod 12457590369460309)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (346044176929453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (346044176929453, 1)] : List FactorBlock).map factorBlockValue).prod) = 12457590369460309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_346044176929453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 12457590369460309) ^ 6228795184730154 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 12457590369460309) ^ 4152530123153436 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 12457590369460309) ^ 36 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_13420426809613079 : Nat.Prime 13420426809613079 := by
  apply lucas_primality 13420426809613079 (7 : ZMod 13420426809613079)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1610227, 1), (4167246857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1610227, 1), (4167246857, 1)] : List FactorBlock).map factorBlockValue).prod) = 13420426809613079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_1610227
      · exact prime_oneHundredFortyFiveEM_4167246857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 13420426809613079) ^ 6710213404806539 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 13420426809613079) ^ 8334493714 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 13420426809613079) ^ 3220454 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_20145586793143873 : Nat.Prime 20145586793143873 := by
  apply lucas_primality 20145586793143873 (7 : ZMod 20145586793143873)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (31, 1), (59, 1), (57367376279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (31, 1), (59, 1), (57367376279, 1)] : List FactorBlock).map factorBlockValue).prod) = 20145586793143873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_31
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_57367376279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20145586793143873) ^ 10072793396571936 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 20145586793143873) ^ 6715195597714624 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 20145586793143873) ^ 649857638488512 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 20145586793143873) ^ 341450623612608 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 20145586793143873) ^ 351168 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_25640814230903491 : Nat.Prime 25640814230903491 := by
  apply lucas_primality 25640814230903491 (2 : ZMod 25640814230903491)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (854693807696783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (854693807696783, 1)] : List FactorBlock).map factorBlockValue).prod) = 25640814230903491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_854693807696783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25640814230903491) ^ 12820407115451745 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25640814230903491) ^ 8546938076967830 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25640814230903491) ^ 5128162846180698 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25640814230903491) ^ 30 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_50476766696390149 : Nat.Prime 50476766696390149 := by
  apply lucas_primality 50476766696390149 (2 : ZMod 50476766696390149)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4206397224699179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4206397224699179, 1)] : List FactorBlock).map factorBlockValue).prod) = 50476766696390149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_4206397224699179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50476766696390149) ^ 25238383348195074 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 50476766696390149) ^ 16825588898796716 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 50476766696390149) ^ 12 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_53433307591108559 : Nat.Prime 53433307591108559 := by
  apply lucas_primality 53433307591108559 (7 : ZMod 53433307591108559)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1601, 1), (19541, 1), (853972619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1601, 1), (19541, 1), (853972619, 1)] : List FactorBlock).map factorBlockValue).prod) = 53433307591108559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_1601
      · exact prime_oneHundredFortyFiveEM_19541
      · exact prime_oneHundredFortyFiveEM_853972619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 53433307591108559) ^ 26716653795554279 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 53433307591108559) ^ 33374957895758 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 53433307591108559) ^ 2734420326038 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 53433307591108559) ^ 62570282 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_56142629097933383 : Nat.Prime 56142629097933383 := by
  apply lucas_primality 56142629097933383 (5 : ZMod 56142629097933383)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8461, 1), (3317730120431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8461, 1), (3317730120431, 1)] : List FactorBlock).map factorBlockValue).prod) = 56142629097933383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_8461
      · exact prime_oneHundredFortyFiveEM_3317730120431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 56142629097933383) ^ 28071314548966691 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 56142629097933383) ^ 6635460240862 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 56142629097933383) ^ 16922 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_76749851526791659 : Nat.Prime 76749851526791659 := by
  apply lucas_primality 76749851526791659 (2 : ZMod 76749851526791659)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (59, 1), (409, 1), (1279, 1), (18019909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (59, 1), (409, 1), (1279, 1), (18019909, 1)] : List FactorBlock).map factorBlockValue).prod) = 76749851526791659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_409
      · exact prime_oneHundredFortyFiveEM_1279
      · exact prime_oneHundredFortyFiveEM_18019909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76749851526791659) ^ 38374925763395829 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76749851526791659) ^ 25583283842263886 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76749851526791659) ^ 3336950066382246 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76749851526791659) ^ 1300844941132062 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76749851526791659) ^ 187652448720762 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76749851526791659) ^ 60007702522902 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76749851526791659) ^ 4259169762 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_78303288274877279 : Nat.Prime 78303288274877279 := by
  apply lucas_primality 78303288274877279 (11 : ZMod 78303288274877279)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (188767, 1), (120796301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (188767, 1), (120796301, 1)] : List FactorBlock).map factorBlockValue).prod) = 78303288274877279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_101
      · exact prime_oneHundredFortyFiveEM_188767
      · exact prime_oneHundredFortyFiveEM_120796301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 78303288274877279) ^ 39151644137438639 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 78303288274877279) ^ 4606075780875134 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 78303288274877279) ^ 775280081929478 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 78303288274877279) ^ 414814497634 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 78303288274877279) ^ 648225878 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_83294430075765959 : Nat.Prime 83294430075765959 := by
  apply lucas_primality 83294430075765959 (7 : ZMod 83294430075765959)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5949602148268997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5949602148268997, 1)] : List FactorBlock).map factorBlockValue).prod) = 83294430075765959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_5949602148268997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 83294430075765959) ^ 41647215037882979 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 83294430075765959) ^ 11899204296537994 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 83294430075765959) ^ 14 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_126803594411166637 : Nat.Prime 126803594411166637 := by
  apply lucas_primality 126803594411166637 (6 : ZMod 126803594411166637)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (167, 1), (197, 1), (709, 1), (151008061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (167, 1), (197, 1), (709, 1), (151008061, 1)] : List FactorBlock).map factorBlockValue).prod) = 126803594411166637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_167
      · exact prime_oneHundredFortyFiveEM_197
      · exact prime_oneHundredFortyFiveEM_709
      · exact prime_oneHundredFortyFiveEM_151008061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 126803594411166637) ^ 63401797205583318 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 126803594411166637) ^ 42267864803722212 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 126803594411166637) ^ 759302960545908 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 126803594411166637) ^ 643673068076988 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 126803594411166637) ^ 178848511158204 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 126803594411166637) ^ 839714076 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_200101966683997069 : Nat.Prime 200101966683997069 := by
  apply lucas_primality 200101966683997069 (6 : ZMod 200101966683997069)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5783, 1), (27259, 1), (35260279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5783, 1), (27259, 1), (35260279, 1)] : List FactorBlock).map factorBlockValue).prod) = 200101966683997069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5783
      · exact prime_oneHundredFortyFiveEM_27259
      · exact prime_oneHundredFortyFiveEM_35260279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 200101966683997069) ^ 100050983341998534 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 200101966683997069) ^ 66700655561332356 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 200101966683997069) ^ 34601758029396 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 200101966683997069) ^ 7340766964452 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 200101966683997069) ^ 5674996692 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_229662409153464871 : Nat.Prime 229662409153464871 := by
  apply lucas_primality 229662409153464871 (11 : ZMod 229662409153464871)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (11795706684821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (59, 1), (11795706684821, 1)] : List FactorBlock).map factorBlockValue).prod) = 229662409153464871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_11795706684821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 229662409153464871) ^ 114831204576732435 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 76554136384488290 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 45932481830692974 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 20878400832133170 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 3892583205990930 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 229662409153464871) ^ 19470 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_281411280302513323 : Nat.Prime 281411280302513323 := by
  apply lucas_primality 281411280302513323 (5 : ZMod 281411280302513323)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (37, 1), (5741, 1), (738464789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (37, 1), (5741, 1), (738464789, 1)] : List FactorBlock).map factorBlockValue).prod) = 281411280302513323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_37
      · exact prime_oneHundredFortyFiveEM_5741
      · exact prime_oneHundredFortyFiveEM_738464789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 281411280302513323) ^ 140705640151256661 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 281411280302513323) ^ 93803760100837774 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 281411280302513323) ^ 21647021561731794 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 281411280302513323) ^ 12235273056631014 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 281411280302513323) ^ 7605710278446306 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 281411280302513323) ^ 49017815764242 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 281411280302513323) ^ 381076098 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_306379258555930627 : Nat.Prime 306379258555930627 := by
  apply lucas_primality 306379258555930627 (2 : ZMod 306379258555930627)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (7297, 1), (27847, 1), (22845079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (7297, 1), (27847, 1), (22845079, 1)] : List FactorBlock).map factorBlockValue).prod) = 306379258555930627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_7297
      · exact prime_oneHundredFortyFiveEM_27847
      · exact prime_oneHundredFortyFiveEM_22845079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 306379258555930627) ^ 153189629277965313 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 306379258555930627) ^ 102126419518643542 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 306379258555930627) ^ 27852659868720966 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 306379258555930627) ^ 41987016384258 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 306379258555930627) ^ 11002235736558 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 306379258555930627) ^ 13411170894 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_356794724615209037 : Nat.Prime 356794724615209037 := by
  apply lucas_primality 356794724615209037 (2 : ZMod 356794724615209037)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (839, 1), (6451, 1), (1267727987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (839, 1), (6451, 1), (1267727987, 1)] : List FactorBlock).map factorBlockValue).prod) = 356794724615209037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_839
      · exact prime_oneHundredFortyFiveEM_6451
      · exact prime_oneHundredFortyFiveEM_1267727987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 356794724615209037) ^ 178397362307604518 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 356794724615209037) ^ 27445748047323772 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 356794724615209037) ^ 425261888695124 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 356794724615209037) ^ 55308436616836 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 356794724615209037) ^ 281444228 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_704476277925837371 : Nat.Prime 704476277925837371 := by
  apply lucas_primality 704476277925837371 (2 : ZMod 704476277925837371)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (37, 1), (61, 1), (997, 1), (1079547257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (37, 1), (61, 1), (997, 1), (1079547257, 1)] : List FactorBlock).map factorBlockValue).prod) = 704476277925837371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_37
      · exact prime_oneHundredFortyFiveEM_61
      · exact prime_oneHundredFortyFiveEM_997
      · exact prime_oneHundredFortyFiveEM_1079547257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 704476277925837371) ^ 352238138962918685 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 140895255585167474 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 24292285445718530 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 19039899403401010 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 11548791441407170 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 706596066124210 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 704476277925837371) ^ 652566410 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_725076667513957051 : Nat.Prime 725076667513957051 := by
  apply lucas_primality 725076667513957051 (3 : ZMod 725076667513957051)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (67, 1), (263, 1), (91440978569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (67, 1), (263, 1), (91440978569, 1)] : List FactorBlock).map factorBlockValue).prod) = 725076667513957051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_67
      · exact prime_oneHundredFortyFiveEM_263
      · exact prime_oneHundredFortyFiveEM_91440978569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 725076667513957051) ^ 362538333756978525 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 725076667513957051) ^ 241692222504652350 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 725076667513957051) ^ 145015333502791410 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 725076667513957051) ^ 10822039813641150 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 725076667513957051) ^ 2756945503855350 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 725076667513957051) ^ 7929450 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_812698794271237267 : Nat.Prime 812698794271237267 := by
  apply lucas_primality 812698794271237267 (2 : ZMod 812698794271237267)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (311, 1), (48392211162989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (311, 1), (48392211162989, 1)] : List FactorBlock).map factorBlockValue).prod) = 812698794271237267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_311
      · exact prime_oneHundredFortyFiveEM_48392211162989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 812698794271237267) ^ 406349397135618633 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 812698794271237267) ^ 270899598090412422 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 812698794271237267) ^ 2613179402801406 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 812698794271237267) ^ 16794 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1381497327482249863 : Nat.Prime 1381497327482249863 := by
  apply lucas_primality 1381497327482249863 (6 : ZMod 1381497327482249863)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (76749851526791659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (76749851526791659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1381497327482249863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_76749851526791659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1381497327482249863) ^ 690748663741124931 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1381497327482249863) ^ 460499109160749954 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1381497327482249863) ^ 18 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2483429385636445577 : Nat.Prime 2483429385636445577 := by
  apply lucas_primality 2483429385636445577 (6 : ZMod 2483429385636445577)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (3313, 1), (15607, 1), (545793397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (3313, 1), (15607, 1), (545793397, 1)] : List FactorBlock).map factorBlockValue).prod) = 2483429385636445577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_3313
      · exact prime_oneHundredFortyFiveEM_15607
      · exact prime_oneHundredFortyFiveEM_545793397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2483429385636445577) ^ 1241714692818222788 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2483429385636445577) ^ 225766307785131416 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2483429385636445577) ^ 749601384134152 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2483429385636445577) ^ 159122790134968 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2483429385636445577) ^ 4550127208 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_5266210878529829827 : Nat.Prime 5266210878529829827 := by
  apply lucas_primality 5266210878529829827 (2 : ZMod 5266210878529829827)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (4561, 1), (14802789757447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (4561, 1), (14802789757447, 1)] : List FactorBlock).map factorBlockValue).prod) = 5266210878529829827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_4561
      · exact prime_oneHundredFortyFiveEM_14802789757447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5266210878529829827) ^ 2633105439264914913 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5266210878529829827) ^ 1755403626176609942 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5266210878529829827) ^ 405093144502294602 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5266210878529829827) ^ 1154617601080866 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5266210878529829827) ^ 355758 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_10986778786910232689 : Nat.Prime 10986778786910232689 := by
  apply lucas_primality 10986778786910232689 (3 : ZMod 10986778786910232689)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (173, 1), (125617, 1), (31597729523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (173, 1), (125617, 1), (31597729523, 1)] : List FactorBlock).map factorBlockValue).prod) = 10986778786910232689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_173
      · exact prime_oneHundredFortyFiveEM_125617
      · exact prime_oneHundredFortyFiveEM_31597729523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10986778786910232689) ^ 5493389393455116344 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10986778786910232689) ^ 63507391831851056 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10986778786910232689) ^ 87462515319664 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 10986778786910232689) ^ 347707856 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_12902145728085127211 : Nat.Prime 12902145728085127211 := by
  apply lucas_primality 12902145728085127211 (2 : ZMod 12902145728085127211)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (120323131, 1), (564363889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (120323131, 1), (564363889, 1)] : List FactorBlock).map factorBlockValue).prod) = 12902145728085127211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_120323131
      · exact prime_oneHundredFortyFiveEM_564363889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12902145728085127211) ^ 6451072864042563605 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12902145728085127211) ^ 2580429145617025442 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12902145728085127211) ^ 679060301478164590 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12902145728085127211) ^ 107229138910 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 12902145728085127211) ^ 22861394890 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_37836657821478463027 : Nat.Prime 37836657821478463027 := by
  apply lucas_primality 37836657821478463027 (2 : ZMod 37836657821478463027)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (773, 1), (8157968482423127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (773, 1), (8157968482423127, 1)] : List FactorBlock).map factorBlockValue).prod) = 37836657821478463027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_773
      · exact prime_oneHundredFortyFiveEM_8157968482423127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37836657821478463027) ^ 18918328910739231513 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 37836657821478463027) ^ 12612219273826154342 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 37836657821478463027) ^ 48947810894538762 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 37836657821478463027) ^ 4638 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_39934878178559326579 : Nat.Prime 39934878178559326579 := by
  apply lucas_primality 39934878178559326579 (12 : ZMod 39934878178559326579)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (11, 1), (2081, 1), (1977966871619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (11, 1), (2081, 1), (1977966871619, 1)] : List FactorBlock).map factorBlockValue).prod) = 39934878178559326579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_2081
      · exact prime_oneHundredFortyFiveEM_1977966871619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 39934878178559326579) ^ 19967439089279663289 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 39934878178559326579) ^ 13311626059519775526 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 39934878178559326579) ^ 5704982596937046654 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 39934878178559326579) ^ 3630443470778120598 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 39934878178559326579) ^ 19190234588447538 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (12 : ZMod 39934878178559326579) ^ 20189862 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_50909808695085878651 : Nat.Prime 50909808695085878651 := by
  apply lucas_primality 50909808695085878651 (6 : ZMod 50909808695085878651)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (138185629, 1), (150373913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (138185629, 1), (150373913, 1)] : List FactorBlock).map factorBlockValue).prod) = 50909808695085878651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_138185629
      · exact prime_oneHundredFortyFiveEM_150373913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 50909808695085878651) ^ 25454904347542939325 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 50909808695085878651) ^ 10181961739017175730 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 50909808695085878651) ^ 7272829813583696950 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 50909808695085878651) ^ 368416086850 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 50909808695085878651) ^ 338554791050 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_2063
      · exact prime_oneHundredFortyFiveEM_15269
      · exact prime_oneHundredFortyFiveEM_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_53863779409500243871 : Nat.Prime 53863779409500243871 := by
  apply lucas_primality 53863779409500243871 (3 : ZMod 53863779409500243871)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (113, 1), (3539, 1), (1496564045849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (113, 1), (3539, 1), (1496564045849, 1)] : List FactorBlock).map factorBlockValue).prod) = 53863779409500243871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_113
      · exact prime_oneHundredFortyFiveEM_3539
      · exact prime_oneHundredFortyFiveEM_1496564045849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 53863779409500243871) ^ 26931889704750121935 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 53863779409500243871) ^ 17954593136500081290 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 53863779409500243871) ^ 10772755881900048774 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 53863779409500243871) ^ 476670614243364990 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 53863779409500243871) ^ 15220056346284330 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 53863779409500243871) ^ 35991630 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_105644708210593840661 : Nat.Prime 105644708210593840661 := by
  apply lucas_primality 105644708210593840661 (2 : ZMod 105644708210593840661)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (229662409153464871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (229662409153464871, 1)] : List FactorBlock).map factorBlockValue).prod) = 105644708210593840661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_229662409153464871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105644708210593840661) ^ 52822354105296920330 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 105644708210593840661) ^ 21128941642118768132 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 105644708210593840661) ^ 4593248183069297420 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 105644708210593840661) ^ 460 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_134367685700296499281 : Nat.Prime 134367685700296499281 := by
  apply lucas_primality 134367685700296499281 (7 : ZMod 134367685700296499281)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (31, 1), (6020057603059879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (31, 1), (6020057603059879, 1)] : List FactorBlock).map factorBlockValue).prod) = 134367685700296499281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_31
      · exact prime_oneHundredFortyFiveEM_6020057603059879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 134367685700296499281) ^ 67183842850148249640 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 134367685700296499281) ^ 44789228566765499760 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 134367685700296499281) ^ 26873537140059299856 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 134367685700296499281) ^ 4334441474203112880 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 134367685700296499281) ^ 22320 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_141256632629283098539 : Nat.Prime 141256632629283098539 := by
  apply lucas_primality 141256632629283098539 (3 : ZMod 141256632629283098539)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (61, 1), (1562538800350469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (61, 1), (1562538800350469, 1)] : List FactorBlock).map factorBlockValue).prod) = 141256632629283098539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_19
      · exact prime_oneHundredFortyFiveEM_61
      · exact prime_oneHundredFortyFiveEM_1562538800350469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 141256632629283098539) ^ 70628316314641549269 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 141256632629283098539) ^ 47085544209761032846 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 141256632629283098539) ^ 10865894817637161426 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 141256632629283098539) ^ 7434559612067531502 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 141256632629283098539) ^ 2315682502119395058 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 141256632629283098539) ^ 90402 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_159739512714237306317 : Nat.Prime 159739512714237306317 := by
  apply lucas_primality 159739512714237306317 (2 : ZMod 159739512714237306317)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (39934878178559326579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (39934878178559326579, 1)] : List FactorBlock).map factorBlockValue).prod) = 159739512714237306317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_39934878178559326579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 159739512714237306317) ^ 79869756357118653158 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 159739512714237306317) ^ 4 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_391480247691406805353 : Nat.Prime 391480247691406805353 := by
  apply lucas_primality 391480247691406805353 (5 : ZMod 391480247691406805353)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2441, 1), (6707117, 1), (996311059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2441, 1), (6707117, 1), (996311059, 1)] : List FactorBlock).map factorBlockValue).prod) = 391480247691406805353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_2441
      · exact prime_oneHundredFortyFiveEM_6707117
      · exact prime_oneHundredFortyFiveEM_996311059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 391480247691406805353) ^ 195740123845703402676 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 391480247691406805353) ^ 130493415897135601784 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 391480247691406805353) ^ 160376996186565672 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 391480247691406805353) ^ 58367887080456 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 391480247691406805353) ^ 392929742328 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_402260752620704829521 : Nat.Prime 402260752620704829521 := by
  apply lucas_primality 402260752620704829521 (3 : ZMod 402260752620704829521)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (733, 1), (6859835481253493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (733, 1), (6859835481253493, 1)] : List FactorBlock).map factorBlockValue).prod) = 402260752620704829521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_733
      · exact prime_oneHundredFortyFiveEM_6859835481253493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 402260752620704829521) ^ 201130376310352414760 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 402260752620704829521) ^ 80452150524140965904 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 402260752620704829521) ^ 548786838500279440 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 402260752620704829521) ^ 58640 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_464267131664867920033 : Nat.Prime 464267131664867920033 := by
  apply lucas_primality 464267131664867920033 (5 : ZMod 464267131664867920033)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 2), (17, 1), (409, 1), (14194771174511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 2), (17, 1), (409, 1), (14194771174511, 1)] : List FactorBlock).map factorBlockValue).prod) = 464267131664867920033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_409
      · exact prime_oneHundredFortyFiveEM_14194771174511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 464267131664867920033) ^ 232133565832433960016 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 464267131664867920033) ^ 154755710554955973344 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 464267131664867920033) ^ 66323875952123988576 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 464267131664867920033) ^ 27309831274403995296 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 464267131664867920033) ^ 1135127461283295648 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 464267131664867920033) ^ 32706912 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_726320058471557000653 : Nat.Prime 726320058471557000653 := by
  apply lucas_primality 726320058471557000653 (2 : ZMod 726320058471557000653)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (71, 1), (389, 1), (221159, 1), (582888253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (71, 1), (389, 1), (221159, 1), (582888253, 1)] : List FactorBlock).map factorBlockValue).prod) = 726320058471557000653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_71
      · exact prime_oneHundredFortyFiveEM_389
      · exact prime_oneHundredFortyFiveEM_221159
      · exact prime_oneHundredFortyFiveEM_582888253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 726320058471557000653) ^ 363160029235778500326 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 726320058471557000653) ^ 242106686157185666884 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 726320058471557000653) ^ 42724709321856294156 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 726320058471557000653) ^ 10229859978472633812 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 726320058471557000653) ^ 1867146679875467868 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 726320058471557000653) ^ 3284153294559828 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 726320058471557000653) ^ 1246070845884 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_817488657180823307167 : Nat.Prime 817488657180823307167 := by
  apply lucas_primality 817488657180823307167 (3 : ZMod 817488657180823307167)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (705127, 1), (818959, 1), (78646559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (705127, 1), (818959, 1), (78646559, 1)] : List FactorBlock).map factorBlockValue).prod) = 817488657180823307167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_705127
      · exact prime_oneHundredFortyFiveEM_818959
      · exact prime_oneHundredFortyFiveEM_78646559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817488657180823307167) ^ 408744328590411653583 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 817488657180823307167) ^ 272496219060274435722 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 817488657180823307167) ^ 1159349531617458 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 817488657180823307167) ^ 998204619743874 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 817488657180823307167) ^ 10394461850274 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1067134547340592194073 : Nat.Prime 1067134547340592194073 := by
  apply lucas_primality 1067134547340592194073 (10 : ZMod 1067134547340592194073)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (263, 1), (26680321, 1), (905238673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (263, 1), (26680321, 1), (905238673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067134547340592194073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_263
      · exact prime_oneHundredFortyFiveEM_26680321
      · exact prime_oneHundredFortyFiveEM_905238673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1067134547340592194073) ^ 533567273670296097036 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1067134547340592194073) ^ 355711515780197398024 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1067134547340592194073) ^ 152447792477227456296 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1067134547340592194073) ^ 4057545807378677544 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1067134547340592194073) ^ 39997065527832 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (10 : ZMod 1067134547340592194073) ^ 1178843303064 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_71
      · exact prime_oneHundredFortyFiveEM_199
      · exact prime_oneHundredFortyFiveEM_52864081
      · exact prime_oneHundredFortyFiveEM_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2015975521298023525661 : Nat.Prime 2015975521298023525661 := by
  apply lucas_primality 2015975521298023525661 (2 : ZMod 2015975521298023525661)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (47, 1), (306379258555930627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (47, 1), (306379258555930627, 1)] : List FactorBlock).map factorBlockValue).prod) = 2015975521298023525661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_47
      · exact prime_oneHundredFortyFiveEM_306379258555930627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2015975521298023525661) ^ 1007987760649011762830 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2015975521298023525661) ^ 403195104259604705132 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2015975521298023525661) ^ 287996503042574789380 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2015975521298023525661) ^ 42893096197830287780 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2015975521298023525661) ^ 6580 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_3440518411667972740747 : Nat.Prime 3440518411667972740747 := by
  apply lucas_primality 3440518411667972740747 (3 : ZMod 3440518411667972740747)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1993, 1), (424416887, 1), (677911001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1993, 1), (424416887, 1), (677911001, 1)] : List FactorBlock).map factorBlockValue).prod) = 3440518411667972740747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_1993
      · exact prime_oneHundredFortyFiveEM_424416887
      · exact prime_oneHundredFortyFiveEM_677911001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3440518411667972740747) ^ 1720259205833986370373 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440518411667972740747) ^ 1146839470555990913582 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440518411667972740747) ^ 1726301260244843322 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440518411667972740747) ^ 8106459749958 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3440518411667972740747) ^ 5075177134746 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_10503910164012437880241 : Nat.Prime 10503910164012437880241 := by
  apply lucas_primality 10503910164012437880241 (29 : ZMod 10503910164012437880241)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (71, 1), (163, 1), (290904508172549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (71, 1), (163, 1), (290904508172549, 1)] : List FactorBlock).map factorBlockValue).prod) = 10503910164012437880241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_71
      · exact prime_oneHundredFortyFiveEM_163
      · exact prime_oneHundredFortyFiveEM_290904508172549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 10503910164012437880241) ^ 5251955082006218940120 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 3501303388004145960080 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 2100782032802487576048 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 807993089539418298480 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 147942396676231519440 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 64441166650383054480 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (29 : ZMod 10503910164012437880241) ^ 36107760 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_10671345473405921940731 : Nat.Prime 10671345473405921940731 := by
  apply lucas_primality 10671345473405921940731 (2 : ZMod 10671345473405921940731)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1067134547340592194073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1067134547340592194073, 1)] : List FactorBlock).map factorBlockValue).prod) = 10671345473405921940731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_1067134547340592194073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10671345473405921940731) ^ 5335672736702960970365 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10671345473405921940731) ^ 2134269094681184388146 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10671345473405921940731) ^ 10 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_10758505716423470501347 : Nat.Prime 10758505716423470501347 := by
  apply lucas_primality 10758505716423470501347 (2 : ZMod 10758505716423470501347)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (14737, 1), (630426284576651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (14737, 1), (630426284576651, 1)] : List FactorBlock).map factorBlockValue).prod) = 10758505716423470501347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_193
      · exact prime_oneHundredFortyFiveEM_14737
      · exact prime_oneHundredFortyFiveEM_630426284576651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10758505716423470501347) ^ 5379252858211735250673 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10758505716423470501347) ^ 3586168572141156833782 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10758505716423470501347) ^ 55743552934836634722 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10758505716423470501347) ^ 730033637539761858 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 10758505716423470501347) ^ 17065446 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_17426787033846349932007 : Nat.Prime 17426787033846349932007 := by
  apply lucas_primality 17426787033846349932007 (6 : ZMod 17426787033846349932007)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (173, 1), (60289, 1), (296287, 1), (72297943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (173, 1), (60289, 1), (296287, 1), (72297943, 1)] : List FactorBlock).map factorBlockValue).prod) = 17426787033846349932007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_173
      · exact prime_oneHundredFortyFiveEM_60289
      · exact prime_oneHundredFortyFiveEM_296287
      · exact prime_oneHundredFortyFiveEM_72297943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17426787033846349932007) ^ 8713393516923174966003 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 17426787033846349932007) ^ 5808929011282116644002 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 17426787033846349932007) ^ 1340522079526642302462 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 17426787033846349932007) ^ 100732873028013583422 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 17426787033846349932007) ^ 289054172964327654 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 17426787033846349932007) ^ 58817251630501338 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 17426787033846349932007) ^ 241041256648842 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_164673621564703547756623 : Nat.Prime 164673621564703547756623 := by
  apply lucas_primality 164673621564703547756623 (3 : ZMod 164673621564703547756623)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (200770543, 1), (983462925481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (200770543, 1), (983462925481, 1)] : List FactorBlock).map factorBlockValue).prod) = 164673621564703547756623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_139
      · exact prime_oneHundredFortyFiveEM_200770543
      · exact prime_oneHundredFortyFiveEM_983462925481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 164673621564703547756623) ^ 82336810782351773878311 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 164673621564703547756623) ^ 54891207188234515918874 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 164673621564703547756623) ^ 1184702313415133437098 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 164673621564703547756623) ^ 820208079851154 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 164673621564703547756623) ^ 167442632862 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_185938401343770373050113 : Nat.Prime 185938401343770373050113 := by
  apply lucas_primality 185938401343770373050113 (3 : ZMod 185938401343770373050113)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (71, 1), (367651, 1), (27824990649587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (71, 1), (367651, 1), (27824990649587, 1)] : List FactorBlock).map factorBlockValue).prod) = 185938401343770373050113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_71
      · exact prime_oneHundredFortyFiveEM_367651
      · exact prime_oneHundredFortyFiveEM_27824990649587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 185938401343770373050113) ^ 92969200671885186525056 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 185938401343770373050113) ^ 2618850723151695395072 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 185938401343770373050113) ^ 505747030046893312 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 185938401343770373050113) ^ 6682424576 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_200178540336590752446227 : Nat.Prime 200178540336590752446227 := by
  apply lucas_primality 200178540336590752446227 (2 : ZMod 200178540336590752446227)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (2021843, 1), (174925715176777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (2021843, 1), (174925715176777, 1)] : List FactorBlock).map factorBlockValue).prod) = 200178540336590752446227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_283
      · exact prime_oneHundredFortyFiveEM_2021843
      · exact prime_oneHundredFortyFiveEM_174925715176777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 200178540336590752446227) ^ 100089270168295376223113 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 200178540336590752446227) ^ 707344665500320680022 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 200178540336590752446227) ^ 99007954790055782 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 200178540336590752446227) ^ 1144363138 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_368921715596727286790009 : Nat.Prime 368921715596727286790009 := by
  apply lucas_primality 368921715596727286790009 (3 : ZMod 368921715596727286790009)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (159715977601, 1), (288732631151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (159715977601, 1), (288732631151, 1)] : List FactorBlock).map factorBlockValue).prod) = 368921715596727286790009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_159715977601
      · exact prime_oneHundredFortyFiveEM_288732631151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 368921715596727286790009) ^ 184460857798363643395004 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 368921715596727286790009) ^ 2309861049208 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 368921715596727286790009) ^ 1277727820808 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_395412456855380888650627 : Nat.Prime 395412456855380888650627 := by
  apply lucas_primality 395412456855380888650627 (2 : ZMod 395412456855380888650627)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (37, 1), (83, 1), (3733, 1), (83312889945613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (37, 1), (83, 1), (3733, 1), (83312889945613, 1)] : List FactorBlock).map factorBlockValue).prod) = 395412456855380888650627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_23
      · exact prime_oneHundredFortyFiveEM_37
      · exact prime_oneHundredFortyFiveEM_83
      · exact prime_oneHundredFortyFiveEM_3733
      · exact prime_oneHundredFortyFiveEM_83312889945613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 395412456855380888650627) ^ 197706228427690444325313 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 395412456855380888650627) ^ 131804152285126962883542 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 395412456855380888650627) ^ 17191845950233951680462 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 395412456855380888650627) ^ 10686823158253537531098 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 395412456855380888650627) ^ 4764005504281697453622 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 395412456855380888650627) ^ 105923508399512694522 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 395412456855380888650627) ^ 4746113802 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_557533403132296893716107 : Nat.Prime 557533403132296893716107 := by
  apply lucas_primality 557533403132296893716107 (2 : ZMod 557533403132296893716107)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (402260752620704829521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (402260752620704829521, 1)] : List FactorBlock).map factorBlockValue).prod) = 557533403132296893716107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_402260752620704829521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 557533403132296893716107) ^ 278766701566148446858053 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 557533403132296893716107) ^ 185844467710765631238702 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 557533403132296893716107) ^ 79647629018899556245158 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 557533403132296893716107) ^ 50684854830208808519646 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 557533403132296893716107) ^ 1386 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_967949511278107631005039 : Nat.Prime 967949511278107631005039 := by
  apply lucas_primality 967949511278107631005039 (3 : ZMod 967949511278107631005039)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (157, 1), (241, 1), (1669035451, 1), (2554578179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (157, 1), (241, 1), (1669035451, 1), (2554578179, 1)] : List FactorBlock).map factorBlockValue).prod) = 967949511278107631005039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_157
      · exact prime_oneHundredFortyFiveEM_241
      · exact prime_oneHundredFortyFiveEM_1669035451
      · exact prime_oneHundredFortyFiveEM_2554578179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 967949511278107631005039) ^ 483974755639053815502519 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 322649837092702543668346 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 6165283511325526312134 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 4016388013602106352718 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 579945447352938 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 967949511278107631005039) ^ 378907766156922 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_2911542284938760033104289 : Nat.Prime 2911542284938760033104289 := by
  apply lucas_primality 2911542284938760033104289 (3 : ZMod 2911542284938760033104289)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (181, 1), (15791, 1), (730339, 1), (43587345661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (181, 1), (15791, 1), (730339, 1), (43587345661, 1)] : List FactorBlock).map factorBlockValue).prod) = 2911542284938760033104289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_181
      · exact prime_oneHundredFortyFiveEM_15791
      · exact prime_oneHundredFortyFiveEM_730339
      · exact prime_oneHundredFortyFiveEM_43587345661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2911542284938760033104289) ^ 1455771142469380016552144 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2911542284938760033104289) ^ 16085868977562210127648 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2911542284938760033104289) ^ 184379854660170985568 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2911542284938760033104289) ^ 3986562794727872992 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2911542284938760033104289) ^ 66797879999008 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_3168034783318104154145983 : Nat.Prime 3168034783318104154145983 := by
  apply lucas_primality 3168034783318104154145983 (6 : ZMod 3168034783318104154145983)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (184711, 1), (13420426809613079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (184711, 1), (13420426809613079, 1)] : List FactorBlock).map factorBlockValue).prod) = 3168034783318104154145983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_71
      · exact prime_oneHundredFortyFiveEM_184711
      · exact prime_oneHundredFortyFiveEM_13420426809613079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3168034783318104154145983) ^ 1584017391659052077072991 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3168034783318104154145983) ^ 1056011594439368051381994 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3168034783318104154145983) ^ 44620208215747945833042 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3168034783318104154145983) ^ 17151305462685514962 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3168034783318104154145983) ^ 236060658 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_4070393631752997720323569 : Nat.Prime 4070393631752997720323569 := by
  apply lucas_primality 4070393631752997720323569 (11 : ZMod 4070393631752997720323569)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (421, 1), (1723, 1), (3262451, 1), (2756388629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (421, 1), (1723, 1), (3262451, 1), (2756388629, 1)] : List FactorBlock).map factorBlockValue).prod) = 4070393631752997720323569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_421
      · exact prime_oneHundredFortyFiveEM_1723
      · exact prime_oneHundredFortyFiveEM_3262451
      · exact prime_oneHundredFortyFiveEM_2756388629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4070393631752997720323569) ^ 2035196815876498860161784 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4070393631752997720323569) ^ 1356797877250999240107856 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4070393631752997720323569) ^ 313107202442538286178736 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4070393631752997720323569) ^ 9668393424591443516208 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4070393631752997720323569) ^ 2362387482154960952016 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4070393631752997720323569) ^ 1247648970590821968 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (11 : ZMod 4070393631752997720323569) ^ 1476712532089392 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_7642830949394081675842507 : Nat.Prime 7642830949394081675842507 := by
  apply lucas_primality 7642830949394081675842507 (3 : ZMod 7642830949394081675842507)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (105243810493, 1), (12103373607107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (105243810493, 1), (12103373607107, 1)] : List FactorBlock).map factorBlockValue).prod) = 7642830949394081675842507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_105243810493
      · exact prime_oneHundredFortyFiveEM_12103373607107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7642830949394081675842507) ^ 3821415474697040837921253 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7642830949394081675842507) ^ 2547610316464693891947502 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7642830949394081675842507) ^ 72620241642642 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7642830949394081675842507) ^ 631462862958 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_13767161756738616446285531 : Nat.Prime 13767161756738616446285531 := by
  apply lucas_primality 13767161756738616446285531 (2 : ZMod 13767161756738616446285531)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (17426787033846349932007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (17426787033846349932007, 1)] : List FactorBlock).map factorBlockValue).prod) = 13767161756738616446285531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_79
      · exact prime_oneHundredFortyFiveEM_17426787033846349932007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13767161756738616446285531) ^ 6883580878369308223142765 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13767161756738616446285531) ^ 2753432351347723289257106 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13767161756738616446285531) ^ 174267870338463499320070 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13767161756738616446285531) ^ 790 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_21609567401349962434028417 : Nat.Prime 21609567401349962434028417 := by
  apply lucas_primality 21609567401349962434028417 (3 : ZMod 21609567401349962434028417)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (149, 1), (22447, 1), (50476766696390149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (149, 1), (22447, 1), (50476766696390149, 1)] : List FactorBlock).map factorBlockValue).prod) = 21609567401349962434028417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_149
      · exact prime_oneHundredFortyFiveEM_22447
      · exact prime_oneHundredFortyFiveEM_50476766696390149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21609567401349962434028417) ^ 10804783700674981217014208 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21609567401349962434028417) ^ 145030653700335318349184 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21609567401349962434028417) ^ 962692894433552921728 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21609567401349962434028417) ^ 428109184 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_36443175636672885201774539 : Nat.Prime 36443175636672885201774539 := by
  apply lucas_primality 36443175636672885201774539 (2 : ZMod 36443175636672885201774539)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (4903, 1), (50909808695085878651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (4903, 1), (50909808695085878651, 1)] : List FactorBlock).map factorBlockValue).prod) = 36443175636672885201774539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_73
      · exact prime_oneHundredFortyFiveEM_4903
      · exact prime_oneHundredFortyFiveEM_50909808695085878651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36443175636672885201774539) ^ 18221587818336442600887269 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36443175636672885201774539) ^ 499221584064012126051706 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36443175636672885201774539) ^ 7432832069482538283046 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36443175636672885201774539) ^ 715838 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_48249000336309949898437217 : Nat.Prime 48249000336309949898437217 := by
  apply lucas_primality 48249000336309949898437217 (3 : ZMod 48249000336309949898437217)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (9439, 1), (159739512714237306317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (9439, 1), (159739512714237306317, 1)] : List FactorBlock).map factorBlockValue).prod) = 48249000336309949898437217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_9439
      · exact prime_oneHundredFortyFiveEM_159739512714237306317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 48249000336309949898437217) ^ 24124500168154974949218608 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 48249000336309949898437217) ^ 5111664406855593802144 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 48249000336309949898437217) ^ 302048 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_103582294981818279147521107 : Nat.Prime 103582294981818279147521107 := by
  apply lucas_primality 103582294981818279147521107 (3 : ZMod 103582294981818279147521107)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6951563, 1), (2483429385636445577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6951563, 1), (2483429385636445577, 1)] : List FactorBlock).map factorBlockValue).prod) = 103582294981818279147521107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_6951563
      · exact prime_oneHundredFortyFiveEM_2483429385636445577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 103582294981818279147521107) ^ 51791147490909139573760553 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 103582294981818279147521107) ^ 34527431660606093049173702 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 103582294981818279147521107) ^ 14900576313818673462 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 103582294981818279147521107) ^ 41709378 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_158290580050701063701890519 : Nat.Prime 158290580050701063701890519 := by
  apply lucas_primality 158290580050701063701890519 (3 : ZMod 158290580050701063701890519)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (59, 1), (167, 1), (3537337, 1), (2772657679301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (59, 1), (167, 1), (3537337, 1), (2772657679301, 1)] : List FactorBlock).map factorBlockValue).prod) = 158290580050701063701890519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_59
      · exact prime_oneHundredFortyFiveEM_167
      · exact prime_oneHundredFortyFiveEM_3537337
      · exact prime_oneHundredFortyFiveEM_2772657679301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 158290580050701063701890519) ^ 79145290025350531850945259 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 158290580050701063701890519) ^ 52763526683567021233963506 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 158290580050701063701890519) ^ 22612940007243009100270074 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 158290580050701063701890519) ^ 12176198465438543361683886 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 158290580050701063701890519) ^ 2682891187300018028845602 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 158290580050701063701890519) ^ 947847784734736908394554 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 158290580050701063701890519) ^ 44748515634982209414 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 158290580050701063701890519) ^ 57089838833118 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_165152888434401976868157449 : Nat.Prime 165152888434401976868157449 := by
  apply lucas_primality 165152888434401976868157449 (3 : ZMod 165152888434401976868157449)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3593, 1), (4159, 1), (1381497327482249863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3593, 1), (4159, 1), (1381497327482249863, 1)] : List FactorBlock).map factorBlockValue).prod) = 165152888434401976868157449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3593
      · exact prime_oneHundredFortyFiveEM_4159
      · exact prime_oneHundredFortyFiveEM_1381497327482249863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 165152888434401976868157449) ^ 82576444217200988434078724 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 165152888434401976868157449) ^ 45965179079989417441736 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 165152888434401976868157449) ^ 39709759181149790062072 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 165152888434401976868157449) ^ 119546296 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_291545405093383081614196313 : Nat.Prime 291545405093383081614196313 := by
  apply lucas_primality 291545405093383081614196313 (3 : ZMod 291545405093383081614196313)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (36443175636672885201774539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (36443175636672885201774539, 1)] : List FactorBlock).map factorBlockValue).prod) = 291545405093383081614196313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_36443175636672885201774539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 291545405093383081614196313) ^ 145772702546691540807098156 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 291545405093383081614196313) ^ 8 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_488400849558146017063098097 : Nat.Prime 488400849558146017063098097 := by
  apply lucas_primality 488400849558146017063098097 (5 : ZMod 488400849558146017063098097)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (14009, 1), (726320058471557000653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (14009, 1), (726320058471557000653, 1)] : List FactorBlock).map factorBlockValue).prod) = 488400849558146017063098097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_14009
      · exact prime_oneHundredFortyFiveEM_726320058471557000653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 488400849558146017063098097) ^ 244200424779073008531549048 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 488400849558146017063098097) ^ 162800283186048672354366032 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 488400849558146017063098097) ^ 34863362806634736031344 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 488400849558146017063098097) ^ 672432 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_672269404685918635251558557 : Nat.Prime 672269404685918635251558557 := by
  apply lucas_primality 672269404685918635251558557 (2 : ZMod 672269404685918635251558557)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 2), (1629923, 1), (356794724615209037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 2), (1629923, 1), (356794724615209037, 1)] : List FactorBlock).map factorBlockValue).prod) = 672269404685918635251558557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_17
      · exact prime_oneHundredFortyFiveEM_1629923
      · exact prime_oneHundredFortyFiveEM_356794724615209037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 672269404685918635251558557) ^ 336134702342959317625779278 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 672269404685918635251558557) ^ 39545259099171684426562268 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 672269404685918635251558557) ^ 412454701655181646772 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 672269404685918635251558557) ^ 1884190988 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_1158302014830467918845590757 : Nat.Prime 1158302014830467918845590757 := by
  apply lucas_primality 1158302014830467918845590757 (2 : ZMod 1158302014830467918845590757)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (193, 1), (347, 1), (4157, 1), (179032871, 1), (1936604699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (193, 1), (347, 1), (4157, 1), (179032871, 1), (1936604699, 1)] : List FactorBlock).map factorBlockValue).prod) = 1158302014830467918845590757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_193
      · exact prime_oneHundredFortyFiveEM_347
      · exact prime_oneHundredFortyFiveEM_4157
      · exact prime_oneHundredFortyFiveEM_179032871
      · exact prime_oneHundredFortyFiveEM_1936604699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1158302014830467918845590757) ^ 579151007415233959422795378 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1158302014830467918845590757) ^ 386100671610155972948530252 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1158302014830467918845590757) ^ 6001564843681180926661092 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1158302014830467918845590757) ^ 3338046152249187086010348 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1158302014830467918845590757) ^ 278638925867324493347508 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1158302014830467918845590757) ^ 6469772887854029436 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1158302014830467918845590757) ^ 598109678980216044 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_4285717454872731299728685801 : Nat.Prime 4285717454872731299728685801 := by
  apply lucas_primality 4285717454872731299728685801 (3 : ZMod 4285717454872731299728685801)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (29, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (29, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 4285717454872731299728685801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_29
      · exact prime_oneHundredFortyFiveEM_171401
      · exact prime_oneHundredFortyFiveEM_714027719
      · exact prime_oneHundredFortyFiveEM_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4285717454872731299728685801) ^ 2142858727436365649864342900 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 857143490974546259945737160 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 147783360512852803438920200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 25004039969852750565800 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 6002172381871818200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4285717454872731299728685801) ^ 709833377373050200 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_17142869819490925198914743207 : Nat.Prime 17142869819490925198914743207 := by
  apply lucas_primality 17142869819490925198914743207 (5 : ZMod 17142869819490925198914743207)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (8231, 1), (150343, 1), (235871, 1), (2258914624817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (8231, 1), (150343, 1), (235871, 1), (2258914624817, 1)] : List FactorBlock).map factorBlockValue).prod) = 17142869819490925198914743207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_13
      · exact prime_oneHundredFortyFiveEM_8231
      · exact prime_oneHundredFortyFiveEM_150343
      · exact prime_oneHundredFortyFiveEM_235871
      · exact prime_oneHundredFortyFiveEM_2258914624817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17142869819490925198914743207) ^ 8571434909745462599457371603 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 1318682293806994246070364862 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 2082720182176032705493226 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 114025061489333891161642 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 72679005979925150607386 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 17142869819490925198914743207) ^ 7588985272464518 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_24489814027844178855592490293 : Nat.Prime 24489814027844178855592490293 := by
  apply lucas_primality 24489814027844178855592490293 (2 : ZMod 24489814027844178855592490293)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (291545405093383081614196313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (291545405093383081614196313, 1)] : List FactorBlock).map factorBlockValue).prod) = 24489814027844178855592490293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_7
      · exact prime_oneHundredFortyFiveEM_291545405093383081614196313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24489814027844178855592490293) ^ 12244907013922089427796245146 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24489814027844178855592490293) ^ 8163271342614726285197496764 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24489814027844178855592490293) ^ 3498544861120596979370355756 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 24489814027844178855592490293) ^ 84 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_28571449699151541998191238683 : Nat.Prime 28571449699151541998191238683 := by
  apply lucas_primality 28571449699151541998191238683 (5 : ZMod 28571449699151541998191238683)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4369146618673, 1), (1089894365833439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4369146618673, 1), (1089894365833439, 1)] : List FactorBlock).map factorBlockValue).prod) = 28571449699151541998191238683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_4369146618673
      · exact prime_oneHundredFortyFiveEM_1089894365833439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 28571449699151541998191238683) ^ 14285724849575770999095619341 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 28571449699151541998191238683) ^ 9523816566383847332730412894 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 28571449699151541998191238683) ^ 6539366195000634 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (5 : ZMod 28571449699151541998191238683) ^ 26214879712038 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_85714349097454625994573716003 : Nat.Prime 85714349097454625994573716003 := by
  apply lucas_primality 85714349097454625994573716003 (2 : ZMod 85714349097454625994573716003)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10529, 1), (4070393631752997720323569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10529, 1), (4070393631752997720323569, 1)] : List FactorBlock).map factorBlockValue).prod) = 85714349097454625994573716003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_10529
      · exact prime_oneHundredFortyFiveEM_4070393631752997720323569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 85714349097454625994573716003) ^ 42857174548727312997286858001 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 85714349097454625994573716003) ^ 8140787263505995440647138 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 85714349097454625994573716003) ^ 21058 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_85714349097454625994573716041 : Nat.Prime 85714349097454625994573716041 := by
  apply lucas_primality 85714349097454625994573716041 (7 : ZMod 85714349097454625994573716041)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (899893, 1), (403945337, 1), (1964983069187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (899893, 1), (403945337, 1), (1964983069187, 1)] : List FactorBlock).map factorBlockValue).prod) = 85714349097454625994573716041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_3
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_899893
      · exact prime_oneHundredFortyFiveEM_403945337
      · exact prime_oneHundredFortyFiveEM_1964983069187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 85714349097454625994573716041) ^ 42857174548727312997286858020 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 85714349097454625994573716041) ^ 28571449699151541998191238680 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 85714349097454625994573716041) ^ 17142869819490925198914743208 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 85714349097454625994573716041) ^ 95249489769844443722280 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 85714349097454625994573716041) ^ 212192941089587638920 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (7 : ZMod 85714349097454625994573716041) ^ 43620909737872920 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_171428698194909251989147432013 : Nat.Prime 171428698194909251989147432013 := by
  apply lucas_primality 171428698194909251989147432013 (2 : ZMod 171428698194909251989147432013)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (283, 1), (13767161756738616446285531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (283, 1), (13767161756738616446285531, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_11
      · exact prime_oneHundredFortyFiveEM_283
      · exact prime_oneHundredFortyFiveEM_13767161756738616446285531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 171428698194909251989147432013) ^ 85714349097454625994573716006 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 171428698194909251989147432013) ^ 15584427108628113817195221092 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 171428698194909251989147432013) ^ 605755117296499123636563364 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (2 : ZMod 171428698194909251989147432013) ^ 12452 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFiveEM_171428698194909251989147432091 : Nat.Prime 171428698194909251989147432091 := by
  apply lucas_primality 171428698194909251989147432091 (6 : ZMod 171428698194909251989147432091)
  · rw [← oneHundredFortyFiveEMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (133073, 1), (406538471, 1), (316877884485823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (133073, 1), (406538471, 1), (316877884485823, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFiveEM_2
      · exact prime_oneHundredFortyFiveEM_5
      · exact prime_oneHundredFortyFiveEM_133073
      · exact prime_oneHundredFortyFiveEM_406538471
      · exact prime_oneHundredFortyFiveEM_316877884485823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 171428698194909251989147432091) ^ 85714349097454625994573716045 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 171428698194909251989147432091) ^ 34285739638981850397829486418 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 171428698194909251989147432091) ^ 1288230506525811035966330 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 171428698194909251989147432091) ^ 421678907221819240790 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide
    · change (6 : ZMod 171428698194909251989147432091) ^ 540992939513830 ≠ 1
      rw [← oneHundredFortyFiveEMFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432000 : Nat.totient 171428698194909251989147432000 = 66206559136762623864821760000 := by
  rw [← show ((([(2, 6), (5, 3), (29, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_29, prime_oneHundredFortyFiveEM_171401, prime_oneHundredFortyFiveEM_714027719, prime_oneHundredFortyFiveEM_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432001 : Nat.totient 171428698194909251989147432001 = 138957120968572655707499182080 := by
  rw [← show ((([(11, 1), (17, 1), (19, 1), (48249000336309949898437217, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_17, prime_oneHundredFortyFiveEM_19, prime_oneHundredFortyFiveEM_48249000336309949898437217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432002 : Nat.totient 171428698194909251989147432002 = 46798719399966588130786558464 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (23, 2), (953, 1), (21283, 1), (126803594411166637, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_23, prime_oneHundredFortyFiveEM_953, prime_oneHundredFortyFiveEM_21283, prime_oneHundredFortyFiveEM_126803594411166637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432003 : Nat.totient 171428698194909251989147432003 = 167229222602467290574309711200 := by
  rw [← show ((([(43, 1), (787, 1), (90229301, 1), (56142629097933383, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_43, prime_oneHundredFortyFiveEM_787, prime_oneHundredFortyFiveEM_90229301, prime_oneHundredFortyFiveEM_56142629097933383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432004 : Nat.totient 171428698194909251989147432004 = 85706208310191119999133047808 := by
  rw [← show ((([(2, 2), (10529, 1), (4070393631752997720323569, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_10529, prime_oneHundredFortyFiveEM_4070393631752997720323569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432005 : Nat.totient 171428698194909251989147432005 = 91428611513137641050403463680 := by
  rw [← show ((([(3, 1), (5, 1), (3321761, 1), (3440518411667972740747, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_3321761, prime_oneHundredFortyFiveEM_3440518411667972740747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432006 : Nat.totient 171428698194909251989147432006 = 85714349097454625994573716002 := by
  rw [← show ((([(2, 1), (85714349097454625994573716003, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_85714349097454625994573716003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432007 : Nat.totient 171428698194909251989147432007 = 169364387303004258978415165440 := by
  rw [← show ((([(89, 1), (1289, 1), (25633, 1), (4347659, 1), (13408669673461, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_89, prime_oneHundredFortyFiveEM_1289, prime_oneHundredFortyFiveEM_25633, prime_oneHundredFortyFiveEM_4347659, prime_oneHundredFortyFiveEM_13408669673461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432008 : Nat.totient 171428698194909251989147432008 = 52020522718556943161599672320 := by
  rw [← show ((([(2, 3), (3, 1), (13, 1), (73, 1), (12377, 1), (958824821, 1), (634236766099, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_13, prime_oneHundredFortyFiveEM_73, prime_oneHundredFortyFiveEM_12377, prime_oneHundredFortyFiveEM_958824821, prime_oneHundredFortyFiveEM_634236766099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432009 : Nat.totient 171428698194909251989147432009 = 146938884165864460599130919376 := by
  rw [← show ((([(7, 1), (122386673323, 1), (200101966683997069, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_122386673323, prime_oneHundredFortyFiveEM_200101966683997069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432010 : Nat.totient 171428698194909251989147432010 = 68540907954166124468955593808 := by
  rw [← show ((([(2, 1), (5, 1), (2243, 1), (7642830949394081675842507, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_2243, prime_oneHundredFortyFiveEM_7642830949394081675842507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432011 : Nat.totient 171428698194909251989147432011 = 114241689722912093163608693760 := by
  rw [← show ((([(3, 2), (2591, 1), (364916653, 1), (20145586793143873, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_2591, prime_oneHundredFortyFiveEM_364916653, prime_oneHundredFortyFiveEM_20145586793143873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432012 : Nat.totient 171428698194909251989147432012 = 77646792308005796757050389200 := by
  rw [← show ((([(2, 2), (11, 1), (283, 1), (13767161756738616446285531, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_283, prime_oneHundredFortyFiveEM_13767161756738616446285531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432013 : Nat.totient 171428698194909251989147432013 = 171428698194909251989147432012 := by
  rw [← show ((([(171428698194909251989147432013, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_171428698194909251989147432013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432014 : Nat.totient 171428698194909251989147432014 = 56952543937748469160798380800 := by
  rw [← show ((([(2, 1), (3, 1), (311, 1), (8609, 1), (10671345473405921940731, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_311, prime_oneHundredFortyFiveEM_8609, prime_oneHundredFortyFiveEM_10671345473405921940731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432015 : Nat.totient 171428698194909251989147432015 = 135181941906193285701469401600 := by
  rw [← show ((([(5, 1), (71, 1), (4597, 1), (10622309, 1), (9889213193728541, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_71, prime_oneHundredFortyFiveEM_4597, prime_oneHundredFortyFiveEM_10622309, prime_oneHundredFortyFiveEM_9889213193728541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432016 : Nat.totient 171428698194909251989147432016 = 73451300974030196724125232000 := by
  rw [← show ((([(2, 4), (7, 1), (4051, 1), (14735723, 1), (25640814230903491, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_4051, prime_oneHundredFortyFiveEM_14735723, prime_oneHundredFortyFiveEM_25640814230903491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432017 : Nat.totient 171428698194909251989147432017 = 111477226409698822512751718400 := by
  rw [← show ((([(3, 1), (41, 1), (5281, 1), (145064807, 1), (1819282674810437, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_41, prime_oneHundredFortyFiveEM_5281, prime_oneHundredFortyFiveEM_145064807, prime_oneHundredFortyFiveEM_1819282674810437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432018 : Nat.totient 171428698194909251989147432018 = 80517047225976725932814561280 := by
  rw [← show ((([(2, 1), (17, 1), (541, 1), (13063, 1), (1402675697, 1), (508636059227, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_17, prime_oneHundredFortyFiveEM_541, prime_oneHundredFortyFiveEM_13063, prime_oneHundredFortyFiveEM_1402675697, prime_oneHundredFortyFiveEM_508636059227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432019 : Nat.totient 171428698194909251989147432019 = 167781026717469791427023330592 := by
  rw [← show ((([(47, 1), (664843, 1), (58677187757, 1), (93496914227, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_47, prime_oneHundredFortyFiveEM_664843, prime_oneHundredFortyFiveEM_58677187757, prime_oneHundredFortyFiveEM_93496914227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432020 : Nat.totient 171428698194909251989147432020 = 43305838222118674295312386560 := by
  rw [← show ((([(2, 2), (3, 5), (5, 1), (19, 1), (17573, 1), (105644708210593840661, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_19, prime_oneHundredFortyFiveEM_17573, prime_oneHundredFortyFiveEM_105644708210593840661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432021 : Nat.totient 171428698194909251989147432021 = 155249976854068016721896169984 := by
  rw [← show ((([(13, 1), (53, 1), (25439, 1), (1559267, 1), (6272544950999753, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_13, prime_oneHundredFortyFiveEM_53, prime_oneHundredFortyFiveEM_25439, prime_oneHundredFortyFiveEM_1559267, prime_oneHundredFortyFiveEM_6272544950999753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432022 : Nat.totient 171428698194909251989147432022 = 85707533929435604696218533888 := by
  rw [← show ((([(2, 1), (12577, 1), (56529077249, 1), (120560370588107, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_12577, prime_oneHundredFortyFiveEM_56529077249, prime_oneHundredFortyFiveEM_120560370588107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432023 : Nat.totient 171428698194909251989147432023 = 89044527113745900453402009600 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (9539, 1), (14105627, 1), (5515390961148161, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_9539, prime_oneHundredFortyFiveEM_14105627, prime_oneHundredFortyFiveEM_5515390961148161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432024 : Nat.totient 171428698194909251989147432024 = 85610667876826202516636876800 := by
  rw [← show ((([(2, 3), (827, 1), (2358401, 1), (10986778786910232689, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_827, prime_oneHundredFortyFiveEM_2358401, prime_oneHundredFortyFiveEM_10986778786910232689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432025 : Nat.totient 171428698194909251989147432025 = 126054433044933236679205708800 := by
  rw [← show ((([(5, 2), (23, 1), (31, 1), (149, 1), (2999, 1), (1069223, 1), (20129035334069, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_23, prime_oneHundredFortyFiveEM_31, prime_oneHundredFortyFiveEM_149, prime_oneHundredFortyFiveEM_2999, prime_oneHundredFortyFiveEM_1069223, prime_oneHundredFortyFiveEM_20129035334069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432026 : Nat.totient 171428698194909251989147432026 = 57140494973101975008708908928 := by
  rw [← show ((([(2, 1), (3, 1), (27967, 1), (158243, 1), (580039043, 1), (11130243337, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_27967, prime_oneHundredFortyFiveEM_158243, prime_oneHundredFortyFiveEM_580039043, prime_oneHundredFortyFiveEM_11130243337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432027 : Nat.totient 171428698194909251989147432027 = 171428634244287406429308815400 := by
  rw [← show ((([(2682307, 1), (4318759631, 1), (14798442555431, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2682307, prime_oneHundredFortyFiveEM_4318759631, prime_oneHundredFortyFiveEM_14798442555431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432028 : Nat.totient 171428698194909251989147432028 = 85714349097453099261895005552 := by
  rw [← show ((([(2, 2), (61020001436509, 1), (702346337918723, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_61020001436509, prime_oneHundredFortyFiveEM_702346337918723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432029 : Nat.totient 171428698194909251989147432029 = 110344727459368208146038959232 := by
  rw [← show ((([(3, 2), (29, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_29, prime_oneHundredFortyFiveEM_607213, prime_oneHundredFortyFiveEM_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432030 : Nat.totient 171428698194909251989147432030 = 58378184929770644796305817600 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (151, 1), (13597, 1), (15233, 1), (78303288274877279, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_151, prime_oneHundredFortyFiveEM_13597, prime_oneHundredFortyFiveEM_15233, prime_oneHundredFortyFiveEM_78303288274877279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432031 : Nat.totient 171428698194909251989147432031 = 169381883968597303685875058688 := by
  rw [← show ((([(97, 1), (607, 1), (2911542284938760033104289, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_97, prime_oneHundredFortyFiveEM_607, prime_oneHundredFortyFiveEM_2911542284938760033104289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432032 : Nat.totient 171428698194909251989147432032 = 56897648006330707033566302208 := by
  rw [← show ((([(2, 5), (3, 1), (233, 1), (22467229, 1), (169347799, 1), (2014314619, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_233, prime_oneHundredFortyFiveEM_22467229, prime_oneHundredFortyFiveEM_169347799, prime_oneHundredFortyFiveEM_2014314619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432033 : Nat.totient 171428698194909251989147432033 = 165747831398697143025475128000 := by
  rw [← show ((([(61, 1), (101, 1), (139, 1), (200178540336590752446227, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_61, prime_oneHundredFortyFiveEM_101, prime_oneHundredFortyFiveEM_139, prime_oneHundredFortyFiveEM_200178540336590752446227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432034 : Nat.totient 171428698194909251989147432034 = 71844390353880283829356592640 := by
  rw [← show ((([(2, 1), (11, 1), (13, 1), (859, 1), (1705568869, 1), (409124106445289, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_13, prime_oneHundredFortyFiveEM_859, prime_oneHundredFortyFiveEM_1705568869, prime_oneHundredFortyFiveEM_409124106445289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432035 : Nat.totient 171428698194909251989147432035 = 86050483799797585312199495168 := by
  rw [← show ((([(3, 1), (5, 1), (17, 1), (672269404685918635251558557, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_17, prime_oneHundredFortyFiveEM_672269404685918635251558557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432036 : Nat.totient 171428698194909251989147432036 = 83397745067793690156882534432 := by
  rw [← show ((([(2, 2), (37, 1), (1158302014830467918845590757, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_37, prime_oneHundredFortyFiveEM_1158302014830467918845590757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432037 : Nat.totient 171428698194909251989147432037 = 146764260365806603185745457664 := by
  rw [← show ((([(7, 1), (1283, 1), (2707, 1), (25057, 1), (281411280302513323, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_1283, prime_oneHundredFortyFiveEM_2707, prime_oneHundredFortyFiveEM_25057, prime_oneHundredFortyFiveEM_281411280302513323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432038 : Nat.totient 171428698194909251989147432038 = 57142899398261980755987812352 := by
  rw [← show ((([(2, 1), (3, 2), (1390510820353, 1), (6849149554957147, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_1390510820353, prime_oneHundredFortyFiveEM_6849149554957147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432039 : Nat.totient 171428698194909251989147432039 = 162396099530762910014052491256 := by
  rw [← show ((([(19, 1), (16183, 1), (557533403132296893716107, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_19, prime_oneHundredFortyFiveEM_16183, prime_oneHundredFortyFiveEM_557533403132296893716107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432040 : Nat.totient 171428698194909251989147432040 = 68571479277963700795658972800 := by
  rw [← show ((([(2, 3), (5, 1), (4285717454872731299728685801, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_4285717454872731299728685801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432041 : Nat.totient 171428698194909251989147432041 = 113711174574632566758491871888 := by
  rw [← show ((([(3, 1), (199, 1), (351259, 1), (817488657180823307167, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_199, prime_oneHundredFortyFiveEM_351259, prime_oneHundredFortyFiveEM_817488657180823307167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432042 : Nat.totient 171428698194909251989147432042 = 84629357336701535342312409120 := by
  rw [← show ((([(2, 1), (79, 1), (3311184798931, 1), (327674783079929, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_79, prime_oneHundredFortyFiveEM_3311184798931, prime_oneHundredFortyFiveEM_327674783079929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432043 : Nat.totient 171428698194909251989147432043 = 169814734350620889651819765760 := by
  rw [← show ((([(107, 1), (16427, 1), (129011, 1), (987713, 1), (765392109809, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_107, prime_oneHundredFortyFiveEM_16427, prime_oneHundredFortyFiveEM_129011, prime_oneHundredFortyFiveEM_987713, prime_oneHundredFortyFiveEM_765392109809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432044 : Nat.totient 171428698194909251989147432044 = 48979628055688357711184980416 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (291545405093383081614196313, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_291545405093383081614196313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432045 : Nat.totient 171428698194909251989147432045 = 124667979332971159722639093760 := by
  rw [← show ((([(5, 1), (11, 1), (16763, 1), (185938401343770373050113, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_16763, prime_oneHundredFortyFiveEM_185938401343770373050113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432046 : Nat.totient 171428698194909251989147432046 = 83720986208921296820031036408 := by
  rw [← show ((([(2, 1), (43, 1), (14111599, 1), (141256632629283098539, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_43, prime_oneHundredFortyFiveEM_14111599, prime_oneHundredFortyFiveEM_141256632629283098539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432047 : Nat.totient 171428698194909251989147432047 = 105494583504559539685629188736 := by
  rw [← show ((([(3, 3), (13, 1), (488400849558146017063098097, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_13, prime_oneHundredFortyFiveEM_488400849558146017063098097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432048 : Nat.totient 171428698194909251989147432048 = 81987638124095523928275659712 := by
  rw [← show ((([(2, 4), (23, 1), (573199883, 1), (812698794271237267, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_23, prime_oneHundredFortyFiveEM_573199883, prime_oneHundredFortyFiveEM_812698794271237267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432049 : Nat.totient 171428698194909251989147432049 = 171372264992141556416508596560 := by
  rw [← show ((([(3467, 1), (24527, 1), (2015975521298023525661, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3467, prime_oneHundredFortyFiveEM_24527, prime_oneHundredFortyFiveEM_2015975521298023525661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432050 : Nat.totient 171428698194909251989147432050 = 45708726364072353823224605760 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (8179, 1), (11649479, 1), (11994594132657967, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_8179, prime_oneHundredFortyFiveEM_11649479, prime_oneHundredFortyFiveEM_11994594132657967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432051 : Nat.totient 171428698194909251989147432051 = 146938884167065073133554941752 := by
  rw [← show ((([(7, 1), (24489814027844178855592490293, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_24489814027844178855592490293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432052 : Nat.totient 171428698194909251989147432052 = 80642117164629020915969961984 := by
  rw [← show ((([(2, 2), (17, 1), (2677, 1), (1097143, 1), (31699207, 1), (27077876857, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_17, prime_oneHundredFortyFiveEM_2677, prime_oneHundredFortyFiveEM_1097143, prime_oneHundredFortyFiveEM_31699207, prime_oneHundredFortyFiveEM_27077876857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432053 : Nat.totient 171428698194909251989147432053 = 112908322736141194686483698688 := by
  rw [← show ((([(3, 1), (83, 1), (355417, 1), (510793, 1), (3792285681927037, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_83, prime_oneHundredFortyFiveEM_355417, prime_oneHundredFortyFiveEM_510793, prime_oneHundredFortyFiveEM_3792285681927037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432054 : Nat.totient 171428698194909251989147432054 = 85543419036412619826245452800 := by
  rw [← show ((([(2, 1), (503, 1), (163337, 1), (1161529157, 1), (898195460401, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_503, prime_oneHundredFortyFiveEM_163337, prime_oneHundredFortyFiveEM_1161529157, prime_oneHundredFortyFiveEM_898195460401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432055 : Nat.totient 171428698194909251989147432055 = 133789300578804967387311144960 := by
  rw [← show ((([(5, 1), (67, 1), (179, 1), (257, 1), (4591, 1), (924527, 1), (2620750481123, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_67, prime_oneHundredFortyFiveEM_179, prime_oneHundredFortyFiveEM_257, prime_oneHundredFortyFiveEM_4591, prime_oneHundredFortyFiveEM_924527, prime_oneHundredFortyFiveEM_2620750481123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432056 : Nat.totient 171428698194909251989147432056 = 49420271858962854094982985600 := by
  rw [← show ((([(2, 3), (3, 2), (11, 2), (31, 1), (59, 1), (10758505716423470501347, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_31, prime_oneHundredFortyFiveEM_59, prime_oneHundredFortyFiveEM_10758505716423470501347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432057 : Nat.totient 171428698194909251989147432057 = 170847329932292836225326336000 := by
  rw [← show ((([(613, 1), (701, 1), (2969, 1), (134367685700296499281, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_613, prime_oneHundredFortyFiveEM_701, prime_oneHundredFortyFiveEM_2969, prime_oneHundredFortyFiveEM_134367685700296499281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432058 : Nat.totient 171428698194909251989147432058 = 65398300328610769520697016320 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (29, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_19, prime_oneHundredFortyFiveEM_29, prime_oneHundredFortyFiveEM_41, prime_oneHundredFortyFiveEM_397, prime_oneHundredFortyFiveEM_13617913, prime_oneHundredFortyFiveEM_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432059 : Nat.totient 171428698194909251989147432059 = 112865481177157605956829622272 := by
  rw [← show ((([(3, 1), (113, 1), (277, 1), (25099219, 1), (85849273, 1), (847241519, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_113, prime_oneHundredFortyFiveEM_277, prime_oneHundredFortyFiveEM_25099219, prime_oneHundredFortyFiveEM_85849273, prime_oneHundredFortyFiveEM_847241519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432060 : Nat.totient 171428698194909251989147432060 = 63288370775631102474799411200 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (8231, 1), (150343, 1), (235871, 1), (2258914624817, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_13, prime_oneHundredFortyFiveEM_8231, prime_oneHundredFortyFiveEM_150343, prime_oneHundredFortyFiveEM_235871, prime_oneHundredFortyFiveEM_2258914624817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432061 : Nat.totient 171428698194909251989147432061 = 171407088627507902026713395712 := by
  rw [← show ((([(7933, 1), (21609567401349962434028417, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_7933, prime_oneHundredFortyFiveEM_21609567401349962434028417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432062 : Nat.totient 171428698194909251989147432062 = 56812593621434280042646162112 := by
  rw [← show ((([(2, 1), (3, 1), (173, 1), (165152888434401976868157449, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_173, prime_oneHundredFortyFiveEM_165152888434401976868157449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432063 : Nat.totient 171428698194909251989147432063 = 171427616070822180984023291520 := by
  rw [← show ((([(158419, 1), (86106285841, 1), (12567283235797, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_158419, prime_oneHundredFortyFiveEM_86106285841, prime_oneHundredFortyFiveEM_12567283235797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432064 : Nat.totient 171428698194909251989147432064 = 85646263501470722293110438912 := by
  rw [← show ((([(2, 7), (1259, 1), (19908373, 1), (53433307591108559, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_1259, prime_oneHundredFortyFiveEM_19908373, prime_oneHundredFortyFiveEM_53433307591108559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432065 : Nat.totient 171428698194909251989147432065 = 77673138442900806243756165120 := by
  rw [← show ((([(3, 2), (5, 1), (7, 1), (197, 1), (263, 1), (10503910164012437880241, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_197, prime_oneHundredFortyFiveEM_263, prime_oneHundredFortyFiveEM_10503910164012437880241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432066 : Nat.totient 171428698194909251989147432066 = 83890637064455781113567300160 := by
  rw [← show ((([(2, 1), (47, 1), (33857809, 1), (53863779409500243871, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_47, prime_oneHundredFortyFiveEM_33857809, prime_oneHundredFortyFiveEM_53863779409500243871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432067 : Nat.totient 171428698194909251989147432067 = 154264946898501741108330064800 := by
  rw [← show ((([(11, 1), (127, 1), (439, 1), (178151971, 1), (1569032607879019, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_127, prime_oneHundredFortyFiveEM_439, prime_oneHundredFortyFiveEM_178151971, prime_oneHundredFortyFiveEM_1569032607879019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432068 : Nat.totient 171428698194909251989147432068 = 57141375140277665172724191744 := by
  rw [← show ((([(2, 2), (3, 1), (37489, 1), (259392040133, 1), (1469067598847, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_37489, prime_oneHundredFortyFiveEM_259392040133, prime_oneHundredFortyFiveEM_1469067598847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432069 : Nat.totient 171428698194909251989147432069 = 161344657101964385542725541568 := by
  rw [← show ((([(17, 2), (7121471219, 1), (83294430075765959, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_17, prime_oneHundredFortyFiveEM_7121471219, prime_oneHundredFortyFiveEM_83294430075765959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432070 : Nat.totient 171428698194909251989147432070 = 68571479277963700795658972824 := by
  rw [← show ((([(2, 1), (5, 1), (17142869819490925198914743207, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_17142869819490925198914743207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432071 : Nat.totient 171428698194909251989147432071 = 109307255927750435803333324800 := by
  rw [← show ((([(3, 1), (23, 1), (11393, 1), (18522282301, 1), (11773398390263, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_23, prime_oneHundredFortyFiveEM_11393, prime_oneHundredFortyFiveEM_18522282301, prime_oneHundredFortyFiveEM_11773398390263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432072 : Nat.totient 171428698194909251989147432072 = 73469442083233548500345974464 := by
  rw [← show ((([(2, 3), (7, 1), (245731852043, 1), (12457590369460309, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_245731852043, prime_oneHundredFortyFiveEM_12457590369460309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432073 : Nat.totient 171428698194909251989147432073 = 153965063745434709165057192000 := by
  rw [← show ((([(13, 2), (37, 1), (37810391, 1), (725076667513957051, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_13, prime_oneHundredFortyFiveEM_37, prime_oneHundredFortyFiveEM_37810391, prime_oneHundredFortyFiveEM_725076667513957051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432074 : Nat.totient 171428698194909251989147432074 = 56064731483461794435709585920 := by
  rw [← show ((([(2, 1), (3, 3), (53, 1), (33657791521, 1), (1779624113521187, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_53, prime_oneHundredFortyFiveEM_33657791521, prime_oneHundredFortyFiveEM_1779624113521187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432075 : Nat.totient 171428698194909251989147432075 = 137135580121615467045581773760 := by
  rw [← show ((([(5, 2), (18587, 1), (368921715596727286790009, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_18587, prime_oneHundredFortyFiveEM_368921715596727286790009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432076 : Nat.totient 171428698194909251989147432076 = 85714349086922204221237771392 := by
  rw [← show ((([(2, 2), (8138142497, 1), (5266210878529829827, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_8138142497, prime_oneHundredFortyFiveEM_5266210878529829827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432077 : Nat.totient 171428698194909251989147432077 = 108270756754679527572093114312 := by
  rw [← show ((([(3, 1), (19, 2), (158290580050701063701890519, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_19, prime_oneHundredFortyFiveEM_158290580050701063701890519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432078 : Nat.totient 171428698194909251989147432078 = 77922135543138388614578502400 := by
  rw [← show ((([(2, 1), (11, 1), (45039781034081, 1), (173007358726229, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_45039781034081, prime_oneHundredFortyFiveEM_173007358726229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432079 : Nat.totient 171428698194909251989147432079 = 146938673583247754469268933632 := by
  rw [← show ((([(7, 1), (1225933, 1), (1746599, 1), (23335867, 1), (490119073, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_1225933, prime_oneHundredFortyFiveEM_1746599, prime_oneHundredFortyFiveEM_23335867, prime_oneHundredFortyFiveEM_490119073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432080 : Nat.totient 171428698194909251989147432080 = 45714268605721882665255579648 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (899893, 1), (403945337, 1), (1964983069187, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_899893, prime_oneHundredFortyFiveEM_403945337, prime_oneHundredFortyFiveEM_1964983069187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432081 : Nat.totient 171428698194909251989147432081 = 168197070333665632978037514240 := by
  rw [← show ((([(73, 1), (193, 1), (23291, 1), (46322533, 1), (11277761949743, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_73, prime_oneHundredFortyFiveEM_193, prime_oneHundredFortyFiveEM_23291, prime_oneHundredFortyFiveEM_46322533, prime_oneHundredFortyFiveEM_11277761949743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432082 : Nat.totient 171428698194909251989147432082 = 85714349097454625994573716040 := by
  rw [← show ((([(2, 1), (85714349097454625994573716041, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_85714349097454625994573716041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432083 : Nat.totient 171428698194909251989147432083 = 113075447678105596916753089008 := by
  rw [← show ((([(3, 2), (103, 1), (1123, 1), (164673621564703547756623, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_103, prime_oneHundredFortyFiveEM_1123, prime_oneHundredFortyFiveEM_164673621564703547756623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432084 : Nat.totient 171428698194909251989147432084 = 85714349021781310349351411544 := by
  rw [← show ((([(2, 2), (1132689223, 1), (37836657821478463027, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_1132689223, prime_oneHundredFortyFiveEM_37836657821478463027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432085 : Nat.totient 171428698194909251989147432085 = 136728629376000128474727859920 := by
  rw [← show ((([(5, 1), (331, 1), (103582294981818279147521107, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_331, prime_oneHundredFortyFiveEM_103582294981818279147521107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432086 : Nat.totient 171428698194909251989147432086 = 41655749697582595029018869760 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (13, 1), (17, 1), (71, 1), (157, 1), (1489, 1), (19429, 1), (57271534030589, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_13, prime_oneHundredFortyFiveEM_17, prime_oneHundredFortyFiveEM_71, prime_oneHundredFortyFiveEM_157, prime_oneHundredFortyFiveEM_1489, prime_oneHundredFortyFiveEM_19429, prime_oneHundredFortyFiveEM_57271534030589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432087 : Nat.totient 171428698194909251989147432087 = 160178049469054551336416824320 := by
  rw [← show ((([(29, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_29, prime_oneHundredFortyFiveEM_31, prime_oneHundredFortyFiveEM_3599009, prime_oneHundredFortyFiveEM_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432088 : Nat.totient 171428698194909251989147432088 = 85712767447627204471018896768 := by
  rw [← show ((([(2, 3), (54193, 1), (395412456855380888650627, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_54193, prime_oneHundredFortyFiveEM_395412456855380888650627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432089 : Nat.totient 171428698194909251989147432089 = 101479979636985306280038528000 := by
  rw [← show ((([(3, 1), (11, 1), (43, 1), (9363521, 1), (12902145728085127211, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_43, prime_oneHundredFortyFiveEM_9363521, prime_oneHundredFortyFiveEM_12902145728085127211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432090 : Nat.totient 171428698194909251989147432090 = 68570963817090578698505713920 := by
  rw [← show ((([(2, 1), (5, 1), (133073, 1), (406538471, 1), (316877884485823, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_133073, prime_oneHundredFortyFiveEM_406538471, prime_oneHundredFortyFiveEM_316877884485823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432091 : Nat.totient 171428698194909251989147432091 = 171428698194909251989147432090 := by
  rw [← show ((([(171428698194909251989147432091, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_171428698194909251989147432091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432092 : Nat.totient 171428698194909251989147432092 = 57142899398289952834233052032 := by
  rw [← show ((([(2, 2), (3, 2), (4369146618673, 1), (1089894365833439, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_4369146618673, prime_oneHundredFortyFiveEM_1089894365833439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432093 : Nat.totient 171428698194909251989147432093 = 146938864667845543208785804032 := by
  rw [← show ((([(7, 2), (7535629, 1), (464267131664867920033, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_7535629, prime_oneHundredFortyFiveEM_464267131664867920033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432094 : Nat.totient 171428698194909251989147432094 = 80640647120862517048393651200 := by
  rw [← show ((([(2, 1), (23, 1), (61, 1), (27617, 1), (7053727, 1), (313617806795011, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_23, prime_oneHundredFortyFiveEM_61, prime_oneHundredFortyFiveEM_27617, prime_oneHundredFortyFiveEM_7053727, prime_oneHundredFortyFiveEM_313617806795011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432095 : Nat.totient 171428698194909251989147432095 = 91420895441194709533163829024 := by
  rw [← show ((([(3, 1), (5, 1), (11807, 1), (967949511278107631005039, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_11807, prime_oneHundredFortyFiveEM_967949511278107631005039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432096 : Nat.totient 171428698194909251989147432096 = 80290673548414031682675767808 := by
  rw [← show ((([(2, 5), (19, 1), (89, 1), (3168034783318104154145983, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_19, prime_oneHundredFortyFiveEM_89, prime_oneHundredFortyFiveEM_3168034783318104154145983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432097 : Nat.totient 171428698194909251989147432097 = 171404402838884330584832409600 := by
  rw [← show ((([(7649, 1), (91009, 1), (3876540901, 1), (63525801517, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_7649, prime_oneHundredFortyFiveEM_91009, prime_oneHundredFortyFiveEM_3876540901, prime_oneHundredFortyFiveEM_63525801517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432098 : Nat.totient 171428698194909251989147432098 = 57142899398303083996382477364 := by
  rw [← show ((([(2, 1), (3, 1), (28571449699151541998191238683, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_28571449699151541998191238683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432099 : Nat.totient 171428698194909251989147432099 = 154382317323614249654986583040 := by
  rw [← show ((([(13, 1), (41, 1), (1179825150919, 1), (272608044935537, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_13, prime_oneHundredFortyFiveEM_41, prime_oneHundredFortyFiveEM_1179825150919, prime_oneHundredFortyFiveEM_272608044935537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432100 : Nat.totient 171428698194909251989147432100 = 53432319824553323132527056000 := by
  rw [← show ((([(2, 2), (5, 2), (7, 1), (11, 1), (31602863, 1), (704476277925837371, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_2, prime_oneHundredFortyFiveEM_5, prime_oneHundredFortyFiveEM_7, prime_oneHundredFortyFiveEM_11, prime_oneHundredFortyFiveEM_31602863, prime_oneHundredFortyFiveEM_704476277925837371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFiveEM_171428698194909251989147432101 : Nat.totient 171428698194909251989147432101 = 113448720854742989687810772480 := by
  rw [← show ((([(3, 4), (137, 1), (39461, 1), (391480247691406805353, 1)] : List FactorBlock).map factorBlockValue).prod) = 171428698194909251989147432101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFiveEM_3, prime_oneHundredFortyFiveEM_137, prime_oneHundredFortyFiveEM_39461, prime_oneHundredFortyFiveEM_391480247691406805353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortyFiveEM : certifiedKill 1 171428698194909251989147431999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortyFiveEM_171428698194909251989147432000, phi_oneHundredFortyFiveEM_171428698194909251989147432001, phi_oneHundredFortyFiveEM_171428698194909251989147432002,
    phi_oneHundredFortyFiveEM_171428698194909251989147432003, phi_oneHundredFortyFiveEM_171428698194909251989147432004, phi_oneHundredFortyFiveEM_171428698194909251989147432005,
    phi_oneHundredFortyFiveEM_171428698194909251989147432006, phi_oneHundredFortyFiveEM_171428698194909251989147432007, phi_oneHundredFortyFiveEM_171428698194909251989147432008,
    phi_oneHundredFortyFiveEM_171428698194909251989147432009, phi_oneHundredFortyFiveEM_171428698194909251989147432010, phi_oneHundredFortyFiveEM_171428698194909251989147432011,
    phi_oneHundredFortyFiveEM_171428698194909251989147432012, phi_oneHundredFortyFiveEM_171428698194909251989147432013, phi_oneHundredFortyFiveEM_171428698194909251989147432014,
    phi_oneHundredFortyFiveEM_171428698194909251989147432015, phi_oneHundredFortyFiveEM_171428698194909251989147432016, phi_oneHundredFortyFiveEM_171428698194909251989147432017,
    phi_oneHundredFortyFiveEM_171428698194909251989147432018, phi_oneHundredFortyFiveEM_171428698194909251989147432019, phi_oneHundredFortyFiveEM_171428698194909251989147432020,
    phi_oneHundredFortyFiveEM_171428698194909251989147432021, phi_oneHundredFortyFiveEM_171428698194909251989147432022, phi_oneHundredFortyFiveEM_171428698194909251989147432023,
    phi_oneHundredFortyFiveEM_171428698194909251989147432024, phi_oneHundredFortyFiveEM_171428698194909251989147432025, phi_oneHundredFortyFiveEM_171428698194909251989147432026,
    phi_oneHundredFortyFiveEM_171428698194909251989147432027, phi_oneHundredFortyFiveEM_171428698194909251989147432028, phi_oneHundredFortyFiveEM_171428698194909251989147432029,
    phi_oneHundredFortyFiveEM_171428698194909251989147432030, phi_oneHundredFortyFiveEM_171428698194909251989147432031, phi_oneHundredFortyFiveEM_171428698194909251989147432032,
    phi_oneHundredFortyFiveEM_171428698194909251989147432033, phi_oneHundredFortyFiveEM_171428698194909251989147432034, phi_oneHundredFortyFiveEM_171428698194909251989147432035,
    phi_oneHundredFortyFiveEM_171428698194909251989147432036, phi_oneHundredFortyFiveEM_171428698194909251989147432037, phi_oneHundredFortyFiveEM_171428698194909251989147432038,
    phi_oneHundredFortyFiveEM_171428698194909251989147432039, phi_oneHundredFortyFiveEM_171428698194909251989147432040, phi_oneHundredFortyFiveEM_171428698194909251989147432041,
    phi_oneHundredFortyFiveEM_171428698194909251989147432042, phi_oneHundredFortyFiveEM_171428698194909251989147432043, phi_oneHundredFortyFiveEM_171428698194909251989147432044,
    phi_oneHundredFortyFiveEM_171428698194909251989147432045, phi_oneHundredFortyFiveEM_171428698194909251989147432046, phi_oneHundredFortyFiveEM_171428698194909251989147432047,
    phi_oneHundredFortyFiveEM_171428698194909251989147432048, phi_oneHundredFortyFiveEM_171428698194909251989147432049, phi_oneHundredFortyFiveEM_171428698194909251989147432050,
    phi_oneHundredFortyFiveEM_171428698194909251989147432051, phi_oneHundredFortyFiveEM_171428698194909251989147432052, phi_oneHundredFortyFiveEM_171428698194909251989147432053,
    phi_oneHundredFortyFiveEM_171428698194909251989147432054, phi_oneHundredFortyFiveEM_171428698194909251989147432055, phi_oneHundredFortyFiveEM_171428698194909251989147432056,
    phi_oneHundredFortyFiveEM_171428698194909251989147432057, phi_oneHundredFortyFiveEM_171428698194909251989147432058, phi_oneHundredFortyFiveEM_171428698194909251989147432059,
    phi_oneHundredFortyFiveEM_171428698194909251989147432060, phi_oneHundredFortyFiveEM_171428698194909251989147432061, phi_oneHundredFortyFiveEM_171428698194909251989147432062,
    phi_oneHundredFortyFiveEM_171428698194909251989147432063, phi_oneHundredFortyFiveEM_171428698194909251989147432064, phi_oneHundredFortyFiveEM_171428698194909251989147432065,
    phi_oneHundredFortyFiveEM_171428698194909251989147432066, phi_oneHundredFortyFiveEM_171428698194909251989147432067, phi_oneHundredFortyFiveEM_171428698194909251989147432068,
    phi_oneHundredFortyFiveEM_171428698194909251989147432069, phi_oneHundredFortyFiveEM_171428698194909251989147432070, phi_oneHundredFortyFiveEM_171428698194909251989147432071,
    phi_oneHundredFortyFiveEM_171428698194909251989147432072, phi_oneHundredFortyFiveEM_171428698194909251989147432073, phi_oneHundredFortyFiveEM_171428698194909251989147432074,
    phi_oneHundredFortyFiveEM_171428698194909251989147432075, phi_oneHundredFortyFiveEM_171428698194909251989147432076, phi_oneHundredFortyFiveEM_171428698194909251989147432077,
    phi_oneHundredFortyFiveEM_171428698194909251989147432078, phi_oneHundredFortyFiveEM_171428698194909251989147432079, phi_oneHundredFortyFiveEM_171428698194909251989147432080,
    phi_oneHundredFortyFiveEM_171428698194909251989147432081, phi_oneHundredFortyFiveEM_171428698194909251989147432082, phi_oneHundredFortyFiveEM_171428698194909251989147432083,
    phi_oneHundredFortyFiveEM_171428698194909251989147432084, phi_oneHundredFortyFiveEM_171428698194909251989147432085, phi_oneHundredFortyFiveEM_171428698194909251989147432086,
    phi_oneHundredFortyFiveEM_171428698194909251989147432087, phi_oneHundredFortyFiveEM_171428698194909251989147432088, phi_oneHundredFortyFiveEM_171428698194909251989147432089,
    phi_oneHundredFortyFiveEM_171428698194909251989147432090, phi_oneHundredFortyFiveEM_171428698194909251989147432091, phi_oneHundredFortyFiveEM_171428698194909251989147432092,
    phi_oneHundredFortyFiveEM_171428698194909251989147432093, phi_oneHundredFortyFiveEM_171428698194909251989147432094, phi_oneHundredFortyFiveEM_171428698194909251989147432095,
    phi_oneHundredFortyFiveEM_171428698194909251989147432096, phi_oneHundredFortyFiveEM_171428698194909251989147432097, phi_oneHundredFortyFiveEM_171428698194909251989147432098,
    phi_oneHundredFortyFiveEM_171428698194909251989147432099, phi_oneHundredFortyFiveEM_171428698194909251989147432100, phi_oneHundredFortyFiveEM_171428698194909251989147432101
    ]

end TotientTailPeriodKiller
end Erdos249257
