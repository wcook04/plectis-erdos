import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetyOneCKFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetyOneCKFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetyOneCKFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetyOneCKFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetyOneCKFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetyOneCKFastPow a n * ninetyOneCKFastPow a n * a else ninetyOneCKFastPow a n * ninetyOneCKFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetyOneCK_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetyOneCK_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetyOneCK_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetyOneCK_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetyOneCK_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetyOneCK_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetyOneCK_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetyOneCK_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetyOneCK_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetyOneCK_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetyOneCK_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetyOneCK_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetyOneCK_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetyOneCK_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetyOneCK_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetyOneCK_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetyOneCK_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetyOneCK_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetyOneCK_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetyOneCK_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetyOneCK_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetyOneCK_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetyOneCK_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetyOneCK_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetyOneCK_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetyOneCK_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetyOneCK_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetyOneCK_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetyOneCK_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetyOneCK_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetyOneCK_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetyOneCK_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetyOneCK_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetyOneCK_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetyOneCK_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetyOneCK_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetyOneCK_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetyOneCK_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetyOneCK_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetyOneCK_173 : Nat.Prime 173 := by norm_num

private theorem prime_ninetyOneCK_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetyOneCK_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetyOneCK_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetyOneCK_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetyOneCK_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetyOneCK_199 : Nat.Prime 199 := by norm_num

private theorem prime_ninetyOneCK_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetyOneCK_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetyOneCK_233 : Nat.Prime 233 := by norm_num

private theorem prime_ninetyOneCK_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetyOneCK_241 : Nat.Prime 241 := by norm_num

private theorem prime_ninetyOneCK_251 : Nat.Prime 251 := by norm_num

private theorem prime_ninetyOneCK_257 : Nat.Prime 257 := by norm_num

private theorem prime_ninetyOneCK_269 : Nat.Prime 269 := by norm_num

private theorem prime_ninetyOneCK_271 : Nat.Prime 271 := by norm_num

private theorem prime_ninetyOneCK_277 : Nat.Prime 277 := by norm_num

private theorem prime_ninetyOneCK_281 : Nat.Prime 281 := by norm_num

private theorem prime_ninetyOneCK_283 : Nat.Prime 283 := by norm_num

private theorem prime_ninetyOneCK_293 : Nat.Prime 293 := by norm_num

private theorem prime_ninetyOneCK_307 : Nat.Prime 307 := by norm_num

private theorem prime_ninetyOneCK_313 : Nat.Prime 313 := by norm_num

private theorem prime_ninetyOneCK_317 : Nat.Prime 317 := by norm_num

private theorem prime_ninetyOneCK_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetyOneCK_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetyOneCK_349 : Nat.Prime 349 := by norm_num

private theorem prime_ninetyOneCK_353 : Nat.Prime 353 := by norm_num

private theorem prime_ninetyOneCK_359 : Nat.Prime 359 := by norm_num

private theorem prime_ninetyOneCK_367 : Nat.Prime 367 := by norm_num

private theorem prime_ninetyOneCK_373 : Nat.Prime 373 := by norm_num

private theorem prime_ninetyOneCK_379 : Nat.Prime 379 := by norm_num

private theorem prime_ninetyOneCK_383 : Nat.Prime 383 := by norm_num

private theorem prime_ninetyOneCK_397 : Nat.Prime 397 := by norm_num

private theorem prime_ninetyOneCK_409 : Nat.Prime 409 := by norm_num

private theorem prime_ninetyOneCK_419 : Nat.Prime 419 := by norm_num

private theorem prime_ninetyOneCK_431 : Nat.Prime 431 := by norm_num

private theorem prime_ninetyOneCK_433 : Nat.Prime 433 := by norm_num

private theorem prime_ninetyOneCK_449 : Nat.Prime 449 := by norm_num

private theorem prime_ninetyOneCK_457 : Nat.Prime 457 := by norm_num

private theorem prime_ninetyOneCK_461 : Nat.Prime 461 := by norm_num

private theorem prime_ninetyOneCK_463 : Nat.Prime 463 := by norm_num

private theorem prime_ninetyOneCK_479 : Nat.Prime 479 := by norm_num

private theorem prime_ninetyOneCK_487 : Nat.Prime 487 := by norm_num

private theorem prime_ninetyOneCK_491 : Nat.Prime 491 := by norm_num

private theorem prime_ninetyOneCK_503 : Nat.Prime 503 := by norm_num

private theorem prime_ninetyOneCK_521 : Nat.Prime 521 := by norm_num

private theorem prime_ninetyOneCK_523 : Nat.Prime 523 := by norm_num

private theorem prime_ninetyOneCK_547 : Nat.Prime 547 := by norm_num

private theorem prime_ninetyOneCK_557 : Nat.Prime 557 := by norm_num

private theorem prime_ninetyOneCK_569 : Nat.Prime 569 := by norm_num

private theorem prime_ninetyOneCK_571 : Nat.Prime 571 := by norm_num

private theorem prime_ninetyOneCK_577 : Nat.Prime 577 := by norm_num

private theorem prime_ninetyOneCK_599 : Nat.Prime 599 := by norm_num

private theorem prime_ninetyOneCK_601 : Nat.Prime 601 := by norm_num

private theorem prime_ninetyOneCK_643 : Nat.Prime 643 := by norm_num

private theorem prime_ninetyOneCK_677 : Nat.Prime 677 := by norm_num

private theorem prime_ninetyOneCK_701 : Nat.Prime 701 := by norm_num

private theorem prime_ninetyOneCK_727 : Nat.Prime 727 := by norm_num

private theorem prime_ninetyOneCK_739 : Nat.Prime 739 := by norm_num

private theorem prime_ninetyOneCK_743 : Nat.Prime 743 := by norm_num

private theorem prime_ninetyOneCK_761 : Nat.Prime 761 := by norm_num

private theorem prime_ninetyOneCK_773 : Nat.Prime 773 := by norm_num

private theorem prime_ninetyOneCK_787 : Nat.Prime 787 := by norm_num

private theorem prime_ninetyOneCK_797 : Nat.Prime 797 := by norm_num

private theorem prime_ninetyOneCK_821 : Nat.Prime 821 := by norm_num

private theorem prime_ninetyOneCK_877 : Nat.Prime 877 := by norm_num

private theorem prime_ninetyOneCK_929 : Nat.Prime 929 := by norm_num

private theorem prime_ninetyOneCK_947 : Nat.Prime 947 := by norm_num

private theorem prime_ninetyOneCK_967 : Nat.Prime 967 := by norm_num

private theorem prime_ninetyOneCK_977 : Nat.Prime 977 := by norm_num

private theorem prime_ninetyOneCK_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_ninetyOneCK_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_ninetyOneCK_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_ninetyOneCK_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_ninetyOneCK_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_ninetyOneCK_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_ninetyOneCK_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_ninetyOneCK_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_ninetyOneCK_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_ninetyOneCK_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_ninetyOneCK_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_ninetyOneCK_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_ninetyOneCK_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_ninetyOneCK_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_ninetyOneCK_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_ninetyOneCK_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_ninetyOneCK_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_ninetyOneCK_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_ninetyOneCK_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_ninetyOneCK_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_ninetyOneCK_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_ninetyOneCK_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_ninetyOneCK_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_ninetyOneCK_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_ninetyOneCK_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_ninetyOneCK_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_ninetyOneCK_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_ninetyOneCK_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_ninetyOneCK_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_ninetyOneCK_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_ninetyOneCK_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_ninetyOneCK_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_ninetyOneCK_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_ninetyOneCK_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_ninetyOneCK_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_ninetyOneCK_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_ninetyOneCK_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_ninetyOneCK_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_ninetyOneCK_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_ninetyOneCK_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_ninetyOneCK_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_ninetyOneCK_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_ninetyOneCK_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_ninetyOneCK_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_ninetyOneCK_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_ninetyOneCK_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_ninetyOneCK_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_ninetyOneCK_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_ninetyOneCK_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_ninetyOneCK_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_ninetyOneCK_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_ninetyOneCK_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_ninetyOneCK_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_ninetyOneCK_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_ninetyOneCK_4139 : Nat.Prime 4139 := by norm_num

private theorem prime_ninetyOneCK_4201 : Nat.Prime 4201 := by norm_num

private theorem prime_ninetyOneCK_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_ninetyOneCK_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_ninetyOneCK_4447 : Nat.Prime 4447 := by norm_num

private theorem prime_ninetyOneCK_4637 : Nat.Prime 4637 := by norm_num

private theorem prime_ninetyOneCK_4663 : Nat.Prime 4663 := by norm_num

private theorem prime_ninetyOneCK_4799 : Nat.Prime 4799 := by norm_num

private theorem prime_ninetyOneCK_5023 : Nat.Prime 5023 := by norm_num

private theorem prime_ninetyOneCK_5101 : Nat.Prime 5101 := by norm_num

private theorem prime_ninetyOneCK_5107 : Nat.Prime 5107 := by norm_num

private theorem prime_ninetyOneCK_5323 : Nat.Prime 5323 := by norm_num

private theorem prime_ninetyOneCK_5431 : Nat.Prime 5431 := by norm_num

private theorem prime_ninetyOneCK_5527 : Nat.Prime 5527 := by norm_num

private theorem prime_ninetyOneCK_5839 : Nat.Prime 5839 := by norm_num

private theorem prime_ninetyOneCK_6043 : Nat.Prime 6043 := by norm_num

private theorem prime_ninetyOneCK_6197 : Nat.Prime 6197 := by norm_num

private theorem prime_ninetyOneCK_6703 : Nat.Prime 6703 := by norm_num

private theorem prime_ninetyOneCK_6983 : Nat.Prime 6983 := by norm_num

private theorem prime_ninetyOneCK_7907 : Nat.Prime 7907 := by norm_num

private theorem prime_ninetyOneCK_8111 : Nat.Prime 8111 := by norm_num

private theorem prime_ninetyOneCK_8167 : Nat.Prime 8167 := by norm_num

private theorem prime_ninetyOneCK_8171 : Nat.Prime 8171 := by norm_num

private theorem prime_ninetyOneCK_8513 : Nat.Prime 8513 := by norm_num

private theorem prime_ninetyOneCK_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_ninetyOneCK_8821 : Nat.Prime 8821 := by norm_num

private theorem prime_ninetyOneCK_9109 : Nat.Prime 9109 := by norm_num

private theorem prime_ninetyOneCK_9323 : Nat.Prime 9323 := by norm_num

private theorem prime_ninetyOneCK_9421 : Nat.Prime 9421 := by norm_num

private theorem prime_ninetyOneCK_9613 : Nat.Prime 9613 := by norm_num

private theorem prime_ninetyOneCK_9929 : Nat.Prime 9929 := by norm_num

private theorem prime_ninetyOneCK_9941 : Nat.Prime 9941 := by norm_num

private theorem prime_ninetyOneCK_9949 : Nat.Prime 9949 := by norm_num

private theorem prime_ninetyOneCK_9967 : Nat.Prime 9967 := by norm_num

private theorem prime_ninetyOneCK_10141 : Nat.Prime 10141 := by norm_num

private theorem prime_ninetyOneCK_10337 : Nat.Prime 10337 := by norm_num

private theorem prime_ninetyOneCK_10463 : Nat.Prime 10463 := by norm_num

private theorem prime_ninetyOneCK_10477 : Nat.Prime 10477 := by norm_num

private theorem prime_ninetyOneCK_10687 : Nat.Prime 10687 := by norm_num

private theorem prime_ninetyOneCK_11279 : Nat.Prime 11279 := by norm_num

private theorem prime_ninetyOneCK_11317 : Nat.Prime 11317 := by norm_num

private theorem prime_ninetyOneCK_11701 : Nat.Prime 11701 := by norm_num

private theorem prime_ninetyOneCK_12689 : Nat.Prime 12689 := by norm_num

private theorem prime_ninetyOneCK_12809 : Nat.Prime 12809 := by norm_num

private theorem prime_ninetyOneCK_12923 : Nat.Prime 12923 := by norm_num

private theorem prime_ninetyOneCK_12983 : Nat.Prime 12983 := by norm_num

private theorem prime_ninetyOneCK_13241 : Nat.Prime 13241 := by norm_num

private theorem prime_ninetyOneCK_13633 : Nat.Prime 13633 := by norm_num

private theorem prime_ninetyOneCK_13789 : Nat.Prime 13789 := by norm_num

private theorem prime_ninetyOneCK_14411 : Nat.Prime 14411 := by norm_num

private theorem prime_ninetyOneCK_14431 : Nat.Prime 14431 := by norm_num

private theorem prime_ninetyOneCK_14593 : Nat.Prime 14593 := by norm_num

private theorem prime_ninetyOneCK_14737 : Nat.Prime 14737 := by norm_num

private theorem prime_ninetyOneCK_15923 : Nat.Prime 15923 := by norm_num

private theorem prime_ninetyOneCK_16111 : Nat.Prime 16111 := by norm_num

private theorem prime_ninetyOneCK_16981 : Nat.Prime 16981 := by norm_num

private theorem prime_ninetyOneCK_18803 : Nat.Prime 18803 := by norm_num

private theorem prime_ninetyOneCK_19961 : Nat.Prime 19961 := by norm_num

private theorem prime_ninetyOneCK_20023 : Nat.Prime 20023 := by norm_num

private theorem prime_ninetyOneCK_20117 : Nat.Prime 20117 := by norm_num

private theorem prime_ninetyOneCK_20479 : Nat.Prime 20479 := by norm_num

private theorem prime_ninetyOneCK_20641 : Nat.Prime 20641 := by norm_num

private theorem prime_ninetyOneCK_21059 : Nat.Prime 21059 := by norm_num

private theorem prime_ninetyOneCK_21139 : Nat.Prime 21139 := by norm_num

private theorem prime_ninetyOneCK_22511 : Nat.Prime 22511 := by norm_num

private theorem prime_ninetyOneCK_22619 : Nat.Prime 22619 := by norm_num

private theorem prime_ninetyOneCK_23041 : Nat.Prime 23041 := by norm_num

private theorem prime_ninetyOneCK_23159 : Nat.Prime 23159 := by norm_num

private theorem prime_ninetyOneCK_24247 : Nat.Prime 24247 := by norm_num

private theorem prime_ninetyOneCK_24317 : Nat.Prime 24317 := by norm_num

private theorem prime_ninetyOneCK_24809 : Nat.Prime 24809 := by norm_num

private theorem prime_ninetyOneCK_25237 : Nat.Prime 25237 := by norm_num

private theorem prime_ninetyOneCK_26053 : Nat.Prime 26053 := by norm_num

private theorem prime_ninetyOneCK_26497 : Nat.Prime 26497 := by norm_num

private theorem prime_ninetyOneCK_26681 : Nat.Prime 26681 := by norm_num

private theorem prime_ninetyOneCK_27739 : Nat.Prime 27739 := by norm_num

private theorem prime_ninetyOneCK_31963 : Nat.Prime 31963 := by norm_num

private theorem prime_ninetyOneCK_33613 : Nat.Prime 33613 := by norm_num

private theorem prime_ninetyOneCK_34781 : Nat.Prime 34781 := by norm_num

private theorem prime_ninetyOneCK_35437 : Nat.Prime 35437 := by norm_num

private theorem prime_ninetyOneCK_36277 : Nat.Prime 36277 := by norm_num

private theorem prime_ninetyOneCK_36493 : Nat.Prime 36493 := by norm_num

private theorem prime_ninetyOneCK_36571 : Nat.Prime 36571 := by norm_num

private theorem prime_ninetyOneCK_36767 : Nat.Prime 36767 := by norm_num

private theorem prime_ninetyOneCK_39983 : Nat.Prime 39983 := by norm_num

private theorem prime_ninetyOneCK_44221 : Nat.Prime 44221 := by norm_num

private theorem prime_ninetyOneCK_46523 : Nat.Prime 46523 := by norm_num

private theorem prime_ninetyOneCK_47093 : Nat.Prime 47093 := by norm_num

private theorem prime_ninetyOneCK_48049 : Nat.Prime 48049 := by norm_num

private theorem prime_ninetyOneCK_48593 : Nat.Prime 48593 := by norm_num

private theorem prime_ninetyOneCK_49789 : Nat.Prime 49789 := by norm_num

private theorem prime_ninetyOneCK_51481 : Nat.Prime 51481 := by norm_num

private theorem prime_ninetyOneCK_52861 : Nat.Prime 52861 := by norm_num

private theorem prime_ninetyOneCK_53611 : Nat.Prime 53611 := by norm_num

private theorem prime_ninetyOneCK_54133 : Nat.Prime 54133 := by norm_num

private theorem prime_ninetyOneCK_56731 : Nat.Prime 56731 := by norm_num

private theorem prime_ninetyOneCK_57853 : Nat.Prime 57853 := by norm_num

private theorem prime_ninetyOneCK_57977 : Nat.Prime 57977 := by norm_num

private theorem prime_ninetyOneCK_63409 : Nat.Prime 63409 := by norm_num

private theorem prime_ninetyOneCK_64667 : Nat.Prime 64667 := by norm_num

private theorem prime_ninetyOneCK_66337 : Nat.Prime 66337 := by norm_num

private theorem prime_ninetyOneCK_68227 : Nat.Prime 68227 := by norm_num

private theorem prime_ninetyOneCK_68351 : Nat.Prime 68351 := by norm_num

private theorem prime_ninetyOneCK_71693 : Nat.Prime 71693 := by norm_num

private theorem prime_ninetyOneCK_72623 : Nat.Prime 72623 := by norm_num

private theorem prime_ninetyOneCK_73259 : Nat.Prime 73259 := by norm_num

private theorem prime_ninetyOneCK_75797 : Nat.Prime 75797 := by norm_num

private theorem prime_ninetyOneCK_80071 : Nat.Prime 80071 := by norm_num

private theorem prime_ninetyOneCK_80803 : Nat.Prime 80803 := by norm_num

private theorem prime_ninetyOneCK_82387 : Nat.Prime 82387 := by norm_num

private theorem prime_ninetyOneCK_87557 : Nat.Prime 87557 := by norm_num

private theorem prime_ninetyOneCK_93077 : Nat.Prime 93077 := by norm_num

private theorem prime_ninetyOneCK_95231 : Nat.Prime 95231 := by norm_num

private theorem prime_ninetyOneCK_96149 : Nat.Prime 96149 := by norm_num

private theorem prime_ninetyOneCK_97127 : Nat.Prime 97127 := by norm_num

private theorem prime_ninetyOneCK_97973 : Nat.Prime 97973 := by norm_num

private theorem prime_ninetyOneCK_98047 : Nat.Prime 98047 := by norm_num

private theorem prime_ninetyOneCK_100847 : Nat.Prime 100847 := by norm_num

private theorem prime_ninetyOneCK_101701 : Nat.Prime 101701 := by norm_num

private theorem prime_ninetyOneCK_109469 : Nat.Prime 109469 := by norm_num

private theorem prime_ninetyOneCK_111959 : Nat.Prime 111959 := by norm_num

private theorem prime_ninetyOneCK_115337 : Nat.Prime 115337 := by norm_num

private theorem prime_ninetyOneCK_119981 : Nat.Prime 119981 := by norm_num

private theorem prime_ninetyOneCK_120097 : Nat.Prime 120097 := by norm_num

private theorem prime_ninetyOneCK_129707 : Nat.Prime 129707 := by norm_num

private theorem prime_ninetyOneCK_135409 : Nat.Prime 135409 := by norm_num

private theorem prime_ninetyOneCK_136963 : Nat.Prime 136963 := by norm_num

private theorem prime_ninetyOneCK_137251 : Nat.Prime 137251 := by norm_num

private theorem prime_ninetyOneCK_144539 : Nat.Prime 144539 := by norm_num

private theorem prime_ninetyOneCK_152417 : Nat.Prime 152417 := by norm_num

private theorem prime_ninetyOneCK_156631 : Nat.Prime 156631 := by norm_num

private theorem prime_ninetyOneCK_159361 : Nat.Prime 159361 := by norm_num

private theorem prime_ninetyOneCK_159569 : Nat.Prime 159569 := by norm_num

private theorem prime_ninetyOneCK_163811 : Nat.Prime 163811 := by norm_num

private theorem prime_ninetyOneCK_166871 : Nat.Prime 166871 := by norm_num

private theorem prime_ninetyOneCK_169733 : Nat.Prime 169733 := by norm_num

private theorem prime_ninetyOneCK_175411 : Nat.Prime 175411 := by norm_num

private theorem prime_ninetyOneCK_178439 : Nat.Prime 178439 := by norm_num

private theorem prime_ninetyOneCK_179591 : Nat.Prime 179591 := by norm_num

private theorem prime_ninetyOneCK_196751 : Nat.Prime 196751 := by norm_num

private theorem prime_ninetyOneCK_208631 : Nat.Prime 208631 := by norm_num

private theorem prime_ninetyOneCK_209857 : Nat.Prime 209857 := by norm_num

private theorem prime_ninetyOneCK_218191 : Nat.Prime 218191 := by norm_num

private theorem prime_ninetyOneCK_232633 : Nat.Prime 232633 := by norm_num

private theorem prime_ninetyOneCK_242083 : Nat.Prime 242083 := by norm_num

private theorem prime_ninetyOneCK_255851 : Nat.Prime 255851 := by norm_num

private theorem prime_ninetyOneCK_284857 : Nat.Prime 284857 := by norm_num

private theorem prime_ninetyOneCK_288467 : Nat.Prime 288467 := by norm_num

private theorem prime_ninetyOneCK_303097 : Nat.Prime 303097 := by norm_num

private theorem prime_ninetyOneCK_307103 : Nat.Prime 307103 := by norm_num

private theorem prime_ninetyOneCK_319313 : Nat.Prime 319313 := by norm_num

private theorem prime_ninetyOneCK_324503 : Nat.Prime 324503 := by norm_num

private theorem prime_ninetyOneCK_333623 : Nat.Prime 333623 := by norm_num

private theorem prime_ninetyOneCK_339187 : Nat.Prime 339187 := by norm_num

private theorem prime_ninetyOneCK_344819 : Nat.Prime 344819 := by norm_num

private theorem prime_ninetyOneCK_355171 : Nat.Prime 355171 := by norm_num

private theorem prime_ninetyOneCK_376759 : Nat.Prime 376759 := by norm_num

private theorem prime_ninetyOneCK_397517 : Nat.Prime 397517 := by norm_num

private theorem prime_ninetyOneCK_438281 : Nat.Prime 438281 := by norm_num

private theorem prime_ninetyOneCK_443167 : Nat.Prime 443167 := by norm_num

private theorem prime_ninetyOneCK_444461 : Nat.Prime 444461 := by norm_num

private theorem prime_ninetyOneCK_480911 : Nat.Prime 480911 := by norm_num

private theorem prime_ninetyOneCK_491297 : Nat.Prime 491297 := by norm_num

private theorem prime_ninetyOneCK_541133 : Nat.Prime 541133 := by norm_num

private theorem prime_ninetyOneCK_568691 : Nat.Prime 568691 := by norm_num

private theorem prime_ninetyOneCK_580997 : Nat.Prime 580997 := by norm_num

private theorem prime_ninetyOneCK_589451 : Nat.Prime 589451 := by norm_num

private theorem prime_ninetyOneCK_597853 : Nat.Prime 597853 := by norm_num

private theorem prime_ninetyOneCK_600091 : Nat.Prime 600091 := by norm_num

private theorem prime_ninetyOneCK_666173 : Nat.Prime 666173 := by norm_num

private theorem prime_ninetyOneCK_684269 : Nat.Prime 684269 := by norm_num

private theorem prime_ninetyOneCK_693179 : Nat.Prime 693179 := by norm_num

private theorem prime_ninetyOneCK_703981 : Nat.Prime 703981 := by norm_num

private theorem prime_ninetyOneCK_725077 : Nat.Prime 725077 := by norm_num

private theorem prime_ninetyOneCK_752627 : Nat.Prime 752627 := by norm_num

private theorem prime_ninetyOneCK_763381 : Nat.Prime 763381 := by norm_num

private theorem prime_ninetyOneCK_897709 : Nat.Prime 897709 := by norm_num

private theorem prime_ninetyOneCK_928267 : Nat.Prime 928267 := by norm_num

private theorem prime_ninetyOneCK_935839 : Nat.Prime 935839 := by norm_num

private theorem prime_ninetyOneCK_944717 : Nat.Prime 944717 := by norm_num

private theorem prime_ninetyOneCK_948659 : Nat.Prime 948659 := by norm_num

private theorem prime_ninetyOneCK_960803 : Nat.Prime 960803 := by norm_num

private theorem prime_ninetyOneCK_963187 : Nat.Prime 963187 := by norm_num

private theorem prime_ninetyOneCK_985723 : Nat.Prime 985723 := by norm_num

private theorem prime_ninetyOneCK_993467 : Nat.Prime 993467 := by norm_num

private theorem prime_ninetyOneCK_1041163 : Nat.Prime 1041163 := by norm_num

private theorem prime_ninetyOneCK_1148387 : Nat.Prime 1148387 := by norm_num

private theorem prime_ninetyOneCK_1277597 : Nat.Prime 1277597 := by norm_num

private theorem prime_ninetyOneCK_1365019 : Nat.Prime 1365019 := by norm_num

private theorem prime_ninetyOneCK_1373027 : Nat.Prime 1373027 := by norm_num

private theorem prime_ninetyOneCK_1374187 : Nat.Prime 1374187 := by norm_num

private theorem prime_ninetyOneCK_1424947 : Nat.Prime 1424947 := by norm_num

private theorem prime_ninetyOneCK_1473011 : Nat.Prime 1473011 := by norm_num

private theorem prime_ninetyOneCK_1555117 : Nat.Prime 1555117 := by norm_num

private theorem prime_ninetyOneCK_1563739 : Nat.Prime 1563739 := by norm_num

private theorem prime_ninetyOneCK_1622591 : Nat.Prime 1622591 := by norm_num

private theorem prime_ninetyOneCK_1655531 : Nat.Prime 1655531 := by norm_num

private theorem prime_ninetyOneCK_1680803 : Nat.Prime 1680803 := by norm_num

private theorem prime_ninetyOneCK_1760659 : Nat.Prime 1760659 := by norm_num

private theorem prime_ninetyOneCK_1780439 : Nat.Prime 1780439 := by norm_num

private theorem prime_ninetyOneCK_1977727 : Nat.Prime 1977727 := by norm_num

private theorem prime_ninetyOneCK_2021119 : Nat.Prime 2021119 := by norm_num

private theorem prime_ninetyOneCK_2079193 : Nat.Prime 2079193 := by norm_num

private theorem prime_ninetyOneCK_2085971 : Nat.Prime 2085971 := by norm_num

private theorem prime_ninetyOneCK_2133973 : Nat.Prime 2133973 := by norm_num

private theorem prime_ninetyOneCK_2136707 : Nat.Prime 2136707 := by norm_num

private theorem prime_ninetyOneCK_2234159 : Nat.Prime 2234159 := by norm_num

private theorem prime_ninetyOneCK_2246641 : Nat.Prime 2246641 := by norm_num

private theorem prime_ninetyOneCK_2274551 : Nat.Prime 2274551 := by norm_num

private theorem prime_ninetyOneCK_2459659 : Nat.Prime 2459659 := by norm_num

private theorem prime_ninetyOneCK_2563079 : Nat.Prime 2563079 := by norm_num

private theorem prime_ninetyOneCK_2577079 : Nat.Prime 2577079 := by norm_num

private theorem prime_ninetyOneCK_2739421 : Nat.Prime 2739421 := by norm_num

private theorem prime_ninetyOneCK_2781703 : Nat.Prime 2781703 := by norm_num

private theorem prime_ninetyOneCK_3094277 : Nat.Prime 3094277 := by norm_num

private theorem prime_ninetyOneCK_3150841 : Nat.Prime 3150841 := by norm_num

private theorem prime_ninetyOneCK_3572183 : Nat.Prime 3572183 := by norm_num

private theorem prime_ninetyOneCK_3904829 : Nat.Prime 3904829 := by norm_num

private theorem prime_ninetyOneCK_3916169 : Nat.Prime 3916169 := by norm_num

private theorem prime_ninetyOneCK_4214117 : Nat.Prime 4214117 := by norm_num

private theorem prime_ninetyOneCK_4251461 : Nat.Prime 4251461 := by norm_num

private theorem prime_ninetyOneCK_4363199 : Nat.Prime 4363199 := by norm_num

private theorem prime_ninetyOneCK_4477391 : Nat.Prime 4477391 := by norm_num

private theorem prime_ninetyOneCK_4710919 : Nat.Prime 4710919 := by norm_num

private theorem prime_ninetyOneCK_5592817 : Nat.Prime 5592817 := by norm_num

private theorem prime_ninetyOneCK_5882257 : Nat.Prime 5882257 := by norm_num

private theorem prime_ninetyOneCK_7343183 : Nat.Prime 7343183 := by norm_num

private theorem prime_ninetyOneCK_7592483 : Nat.Prime 7592483 := by norm_num

private theorem prime_ninetyOneCK_8942803 : Nat.Prime 8942803 := by norm_num

private theorem prime_ninetyOneCK_10017361 : Nat.Prime 10017361 := by norm_num

private theorem prime_ninetyOneCK_10424569 : Nat.Prime 10424569 := by norm_num

private theorem prime_ninetyOneCK_11047583 : Nat.Prime 11047583 := by norm_num

private theorem prime_ninetyOneCK_11781949 : Nat.Prime 11781949 := by norm_num

private theorem prime_ninetyOneCK_11808707 : Nat.Prime 11808707 := by norm_num

private theorem prime_ninetyOneCK_12933989 : Nat.Prime 12933989 := by norm_num

private theorem prime_ninetyOneCK_13924957 : Nat.Prime 13924957 := by norm_num

private theorem prime_ninetyOneCK_13978967 : Nat.Prime 13978967 := by norm_num

private theorem prime_ninetyOneCK_14321921 : Nat.Prime 14321921 := by norm_num

private theorem prime_ninetyOneCK_15590191 : Nat.Prime 15590191 := by norm_num

private theorem prime_ninetyOneCK_16382341 : Nat.Prime 16382341 := by norm_num

private theorem prime_ninetyOneCK_17034581 : Nat.Prime 17034581 := by norm_num

private theorem prime_ninetyOneCK_17207497 : Nat.Prime 17207497 := by norm_num

private theorem prime_ninetyOneCK_17694779 : Nat.Prime 17694779 := by norm_num

private theorem prime_ninetyOneCK_17935987 : Nat.Prime 17935987 := by norm_num

private theorem prime_ninetyOneCK_18108697 : Nat.Prime 18108697 := by norm_num

private theorem prime_ninetyOneCK_18183433 : Nat.Prime 18183433 := by norm_num

private theorem prime_ninetyOneCK_19671307 : Nat.Prime 19671307 := by norm_num

private theorem prime_ninetyOneCK_19953701 : Nat.Prime 19953701 := by norm_num

private theorem prime_ninetyOneCK_22028423 : Nat.Prime 22028423 := by norm_num

private theorem prime_ninetyOneCK_23911417 : Nat.Prime 23911417 := by norm_num

private theorem prime_ninetyOneCK_24549449 : Nat.Prime 24549449 := by norm_num

private theorem prime_ninetyOneCK_24989773 : Nat.Prime 24989773 := by norm_num

private theorem prime_ninetyOneCK_25049971 : Nat.Prime 25049971 := by norm_num

private theorem prime_ninetyOneCK_25388651 : Nat.Prime 25388651 := by norm_num

private theorem prime_ninetyOneCK_25557079 : Nat.Prime 25557079 := by norm_num

private theorem prime_ninetyOneCK_28758187 : Nat.Prime 28758187 := by norm_num

private theorem prime_ninetyOneCK_28889209 : Nat.Prime 28889209 := by norm_num

private theorem prime_ninetyOneCK_43310299 : Nat.Prime 43310299 := by
  apply lucas_primality 43310299 (3 : ZMod 43310299)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (727, 1), (9929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (727, 1), (9929, 1)] : List FactorBlock).map factorBlockValue).prod) = 43310299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_727
      · exact prime_ninetyOneCK_9929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 43310299) ^ 21655149 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43310299) ^ 14436766 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43310299) ^ 59574 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43310299) ^ 4362 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_44226257 : Nat.Prime 44226257 := by
  apply lucas_primality 44226257 (3 : ZMod 44226257)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1327, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1327, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) = 44226257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1327
      · exact prime_ninetyOneCK_2083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 44226257) ^ 22113128 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 44226257) ^ 33328 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 44226257) ^ 21232 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_47614289 : Nat.Prime 47614289 := by
  apply lucas_primality 47614289 (3 : ZMod 47614289)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (89, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (89, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 47614289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_89
      · exact prime_ninetyOneCK_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 47614289) ^ 23807144 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 47614289) ^ 1641872 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 47614289) ^ 534992 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 47614289) ^ 41296 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_48473981 : Nat.Prime 48473981 := by
  apply lucas_primality 48473981 (3 : ZMod 48473981)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (239, 1), (10141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (239, 1), (10141, 1)] : List FactorBlock).map factorBlockValue).prod) = 48473981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_239
      · exact prime_ninetyOneCK_10141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 48473981) ^ 24236990 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48473981) ^ 9694796 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48473981) ^ 202820 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48473981) ^ 4780 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_51979409 : Nat.Prime 51979409 := by
  apply lucas_primality 51979409 (6 : ZMod 51979409)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (269, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (269, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) = 51979409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_269
      · exact prime_ninetyOneCK_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 51979409) ^ 25989704 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 51979409) ^ 3998416 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 51979409) ^ 193232 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 51979409) ^ 55952 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_52295129 : Nat.Prime 52295129 := by
  apply lucas_primality 52295129 (3 : ZMod 52295129)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 2), (22619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 2), (22619, 1)] : List FactorBlock).map factorBlockValue).prod) = 52295129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_22619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 52295129) ^ 26147564 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 52295129) ^ 3076184 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 52295129) ^ 2312 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_55769849 : Nat.Prime 55769849 := by
  apply lucas_primality 55769849 (3 : ZMod 55769849)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (303097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (303097, 1)] : List FactorBlock).map factorBlockValue).prod) = 55769849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_303097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55769849) ^ 27884924 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 55769849) ^ 2424776 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 55769849) ^ 184 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_58016957 : Nat.Prime 58016957 := by
  apply lucas_primality 58016957 (2 : ZMod 58016957)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (763381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (763381, 1)] : List FactorBlock).map factorBlockValue).prod) = 58016957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_763381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58016957) ^ 29008478 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 58016957) ^ 3053524 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 58016957) ^ 76 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_61790243 : Nat.Prime 61790243 := by
  apply lucas_primality 61790243 (2 : ZMod 61790243)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 1), (47, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 1), (47, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) = 61790243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_47
      · exact prime_ninetyOneCK_1193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61790243) ^ 30895121 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 61790243) ^ 3252118 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 61790243) ^ 2130698 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 61790243) ^ 1314686 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 61790243) ^ 51794 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_61849897 : Nat.Prime 61849897 := by
  apply lucas_primality 61849897 (5 : ZMod 61849897)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2577079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2577079, 1)] : List FactorBlock).map factorBlockValue).prod) = 61849897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_2577079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 61849897) ^ 30924948 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 61849897) ^ 20616632 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 61849897) ^ 24 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_72733733 : Nat.Prime 72733733 := by
  apply lucas_primality 72733733 (2 : ZMod 72733733)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18183433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18183433, 1)] : List FactorBlock).map factorBlockValue).prod) = 72733733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_18183433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 72733733) ^ 36366866 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 72733733) ^ 4 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_72785633 : Nat.Prime 72785633 := by
  apply lucas_primality 72785633 (3 : ZMod 72785633)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2274551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2274551, 1)] : List FactorBlock).map factorBlockValue).prod) = 72785633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_2274551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 72785633) ^ 36392816 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 72785633) ^ 32 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_74280181 : Nat.Prime 74280181 := by
  apply lucas_primality 74280181 (7 : ZMod 74280181)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (95231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (95231, 1)] : List FactorBlock).map factorBlockValue).prod) = 74280181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_95231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 74280181) ^ 37140090 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 74280181) ^ 24760060 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 74280181) ^ 14856036 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 74280181) ^ 5713860 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 74280181) ^ 780 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_75128587 : Nat.Prime 75128587 := by
  apply lucas_primality 75128587 (3 : ZMod 75128587)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (963187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (963187, 1)] : List FactorBlock).map factorBlockValue).prod) = 75128587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_963187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75128587) ^ 37564293 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75128587) ^ 25042862 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75128587) ^ 5779122 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75128587) ^ 78 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_83898049 : Nat.Prime 83898049 := by
  apply lucas_primality 83898049 (17 : ZMod 83898049)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13, 1), (33613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13, 1), (33613, 1)] : List FactorBlock).map factorBlockValue).prod) = 83898049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_33613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 83898049) ^ 41949024 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 83898049) ^ 27966016 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 83898049) ^ 6453696 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 83898049) ^ 2496 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_84209429 : Nat.Prime 84209429 := by
  apply lucas_primality 84209429 (2 : ZMod 84209429)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (196751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (196751, 1)] : List FactorBlock).map factorBlockValue).prod) = 84209429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_107
      · exact prime_ninetyOneCK_196751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 84209429) ^ 42104714 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84209429) ^ 787004 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84209429) ^ 428 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_91904221 : Nat.Prime 91904221 := by
  apply lucas_primality 91904221 (18 : ZMod 91904221)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (56731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (56731, 1)] : List FactorBlock).map factorBlockValue).prod) = 91904221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_56731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (18 : ZMod 91904221) ^ 45952110 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (18 : ZMod 91904221) ^ 30634740 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (18 : ZMod 91904221) ^ 18380844 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (18 : ZMod 91904221) ^ 1620 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_96864301 : Nat.Prime 96864301 := by
  apply lucas_primality 96864301 (2 : ZMod 96864301)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (13, 1), (17, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (13, 1), (17, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) = 96864301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 96864301) ^ 48432150 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 96864301) ^ 32288100 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 96864301) ^ 19372860 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 96864301) ^ 7451100 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 96864301) ^ 5697900 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 96864301) ^ 198900 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_104590259 : Nat.Prime 104590259 := by
  apply lucas_primality 104590259 (2 : ZMod 104590259)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52295129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52295129, 1)] : List FactorBlock).map factorBlockValue).prod) = 104590259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_52295129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 104590259) ^ 52295129 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 104590259) ^ 2 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_105077827 : Nat.Prime 105077827 := by
  apply lucas_primality 105077827 (2 : ZMod 105077827)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (409, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (409, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) = 105077827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_409
      · exact prime_ninetyOneCK_2039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105077827) ^ 52538913 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105077827) ^ 35025942 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105077827) ^ 15011118 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105077827) ^ 256914 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105077827) ^ 51534 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_106149529 : Nat.Prime 106149529 := by
  apply lucas_primality 106149529 (11 : ZMod 106149529)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (163811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (163811, 1)] : List FactorBlock).map factorBlockValue).prod) = 106149529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_163811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 106149529) ^ 53074764 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 106149529) ^ 35383176 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 106149529) ^ 648 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_111453149 : Nat.Prime 111453149 := by
  apply lucas_primality 111453149 (2 : ZMod 111453149)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (960803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (960803, 1)] : List FactorBlock).map factorBlockValue).prod) = 111453149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_960803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111453149) ^ 55726574 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 111453149) ^ 3843212 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 111453149) ^ 116 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_119223763 : Nat.Prime 119223763 := by
  apply lucas_primality 119223763 (2 : ZMod 119223763)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (599, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (599, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 119223763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_599
      · exact prime_ninetyOneCK_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 119223763) ^ 59611881 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 119223763) ^ 39741254 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 119223763) ^ 17031966 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 119223763) ^ 199038 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 119223763) ^ 176106 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_136756897 : Nat.Prime 136756897 := by
  apply lucas_primality 136756897 (10 : ZMod 136756897)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (241, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (241, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 136756897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_241
      · exact prime_ninetyOneCK_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 136756897) ^ 68378448 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 136756897) ^ 45585632 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 136756897) ^ 5945952 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 136756897) ^ 567456 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 136756897) ^ 532128 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_149938639 : Nat.Prime 149938639 := by
  apply lucas_primality 149938639 (6 : ZMod 149938639)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24989773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24989773, 1)] : List FactorBlock).map factorBlockValue).prod) = 149938639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_24989773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 149938639) ^ 74969319 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 149938639) ^ 49979546 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 149938639) ^ 6 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_155558467 : Nat.Prime 155558467 := by
  apply lucas_primality 155558467 (7 : ZMod 155558467)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (72623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (72623, 1)] : List FactorBlock).map factorBlockValue).prod) = 155558467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_72623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 155558467) ^ 77779233 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 155558467) ^ 51852822 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 155558467) ^ 22222638 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 155558467) ^ 9150498 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 155558467) ^ 2142 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_163835053 : Nat.Prime 163835053 := by
  apply lucas_primality 163835053 (5 : ZMod 163835053)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (293, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (293, 1), (2741, 1)] : List FactorBlock).map factorBlockValue).prod) = 163835053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_293
      · exact prime_ninetyOneCK_2741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 163835053) ^ 81917526 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 163835053) ^ 54611684 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 163835053) ^ 9637356 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 163835053) ^ 559164 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 163835053) ^ 59772 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_164100161 : Nat.Prime 164100161 := by
  apply lucas_primality 164100161 (21 : ZMod 164100161)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (73259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (73259, 1)] : List FactorBlock).map factorBlockValue).prod) = 164100161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_73259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 164100161) ^ 82050080 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 164100161) ^ 32820032 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 164100161) ^ 23442880 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 164100161) ^ 2240 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_170108047 : Nat.Prime 170108047 := by
  apply lucas_primality 170108047 (3 : ZMod 170108047)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (23, 1), (136963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (23, 1), (136963, 1)] : List FactorBlock).map factorBlockValue).prod) = 170108047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_136963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 170108047) ^ 85054023 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 170108047) ^ 56702682 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 170108047) ^ 7396002 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 170108047) ^ 1242 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_179112889 : Nat.Prime 179112889 := by
  apply lucas_primality 179112889 (11 : ZMod 179112889)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (43, 1), (57853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (43, 1), (57853, 1)] : List FactorBlock).map factorBlockValue).prod) = 179112889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_43
      · exact prime_ninetyOneCK_57853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 179112889) ^ 89556444 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 179112889) ^ 59704296 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 179112889) ^ 4165416 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 179112889) ^ 3096 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_187834483 : Nat.Prime 187834483 := by
  apply lucas_primality 187834483 (5 : ZMod 187834483)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (948659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (948659, 1)] : List FactorBlock).map factorBlockValue).prod) = 187834483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_948659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 187834483) ^ 93917241 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 187834483) ^ 62611494 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 187834483) ^ 17075862 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 187834483) ^ 198 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_205728337 : Nat.Prime 205728337 := by
  apply lucas_primality 205728337 (5 : ZMod 205728337)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod) = 205728337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_14431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 205728337) ^ 102864168 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 205728337) ^ 68576112 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 205728337) ^ 18702576 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 205728337) ^ 14256 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_213004567 : Nat.Prime 213004567 := by
  apply lucas_primality 213004567 (3 : ZMod 213004567)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (438281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (438281, 1)] : List FactorBlock).map factorBlockValue).prod) = 213004567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_438281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 213004567) ^ 106502283 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 213004567) ^ 71001522 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 213004567) ^ 486 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_222778403 : Nat.Prime 222778403 := by
  apply lucas_primality 222778403 (5 : ZMod 222778403)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (47, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (47, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 222778403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_47
      · exact prime_ninetyOneCK_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 222778403) ^ 111389201 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 222778403) ^ 31825486 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 222778403) ^ 20252582 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 222778403) ^ 4739966 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 222778403) ^ 50666 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_259282157 : Nat.Prime 259282157 := by
  apply lucas_primality 259282157 (3 : ZMod 259282157)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (319313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (319313, 1)] : List FactorBlock).map factorBlockValue).prod) = 259282157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_319313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 259282157) ^ 129641078 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 259282157) ^ 37040308 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 259282157) ^ 8940764 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 259282157) ^ 812 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_268963109 : Nat.Prime 268963109 := by
  apply lucas_primality 268963109 (2 : ZMod 268963109)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (1563739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (1563739, 1)] : List FactorBlock).map factorBlockValue).prod) = 268963109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_43
      · exact prime_ninetyOneCK_1563739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 268963109) ^ 134481554 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 268963109) ^ 6254956 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 268963109) ^ 172 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_293813573 : Nat.Prime 293813573 := by
  apply lucas_primality 293813573 (2 : ZMod 293813573)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (251, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (251, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod) = 293813573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_251
      · exact prime_ninetyOneCK_22511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 293813573) ^ 146906786 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 293813573) ^ 22601044 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 293813573) ^ 1170572 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 293813573) ^ 13052 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_314654917 : Nat.Prime 314654917 := by
  apply lucas_primality 314654917 (2 : ZMod 314654917)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1039, 1), (25237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1039, 1), (25237, 1)] : List FactorBlock).map factorBlockValue).prod) = 314654917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_1039
      · exact prime_ninetyOneCK_25237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 314654917) ^ 157327458 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 314654917) ^ 104884972 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 314654917) ^ 302844 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 314654917) ^ 12468 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_315837031 : Nat.Prime 315837031 := by
  apply lucas_primality 315837031 (22 : ZMod 315837031)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (59, 1), (178439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (59, 1), (178439, 1)] : List FactorBlock).map factorBlockValue).prod) = 315837031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_59
      · exact prime_ninetyOneCK_178439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 315837031) ^ 157918515 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (22 : ZMod 315837031) ^ 105279010 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (22 : ZMod 315837031) ^ 63167406 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (22 : ZMod 315837031) ^ 5353170 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (22 : ZMod 315837031) ^ 1770 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_368237953 : Nat.Prime 368237953 := by
  apply lucas_primality 368237953 (5 : ZMod 368237953)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (17, 1), (18803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (17, 1), (18803, 1)] : List FactorBlock).map factorBlockValue).prod) = 368237953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_18803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 368237953) ^ 184118976 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 368237953) ^ 122745984 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 368237953) ^ 21661056 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 368237953) ^ 19584 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_371099383 : Nat.Prime 371099383 := by
  apply lucas_primality 371099383 (3 : ZMod 371099383)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61849897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61849897, 1)] : List FactorBlock).map factorBlockValue).prod) = 371099383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_61849897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 371099383) ^ 185549691 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 371099383) ^ 123699794 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 371099383) ^ 6 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_426587507 : Nat.Prime 426587507 := by
  apply lucas_primality 426587507 (2 : ZMod 426587507)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 1), (521, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 1), (521, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) = 426587507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_521
      · exact prime_ninetyOneCK_743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 426587507) ^ 213293753 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 426587507) ^ 22451974 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 426587507) ^ 14709914 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 426587507) ^ 818786 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 426587507) ^ 574142 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_428066627 : Nat.Prime 428066627 := by
  apply lucas_primality 428066627 (2 : ZMod 428066627)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (97, 1), (169733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (97, 1), (169733, 1)] : List FactorBlock).map factorBlockValue).prod) = 428066627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_97
      · exact prime_ninetyOneCK_169733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 428066627) ^ 214033313 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 428066627) ^ 32928202 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 428066627) ^ 4413058 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 428066627) ^ 2522 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_498877723 : Nat.Prime 498877723 := by
  apply lucas_primality 498877723 (5 : ZMod 498877723)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 3), (80803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 3), (80803, 1)] : List FactorBlock).map factorBlockValue).prod) = 498877723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_80803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 498877723) ^ 249438861 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 498877723) ^ 166292574 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 498877723) ^ 71268246 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 498877723) ^ 6174 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_530640001 : Nat.Prime 530640001 := by
  apply lucas_primality 530640001 (19 : ZMod 530640001)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 4), (11, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 4), (11, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) = 530640001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_67
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 530640001) ^ 265320000 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 530640001) ^ 176880000 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 530640001) ^ 106128000 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 530640001) ^ 48240000 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 530640001) ^ 7920000 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_534427681 : Nat.Prime 534427681 := by
  apply lucas_primality 534427681 (11 : ZMod 534427681)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (269, 1), (4139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (269, 1), (4139, 1)] : List FactorBlock).map factorBlockValue).prod) = 534427681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_269
      · exact prime_ninetyOneCK_4139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 534427681) ^ 267213840 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 534427681) ^ 178142560 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 534427681) ^ 106885536 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 534427681) ^ 1986720 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 534427681) ^ 129120 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_585502529 : Nat.Prime 585502529 := by
  apply lucas_primality 585502529 (3 : ZMod 585502529)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 2), (54133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 2), (54133, 1)] : List FactorBlock).map factorBlockValue).prod) = 585502529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_54133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 585502529) ^ 292751264 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 585502529) ^ 45038656 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 585502529) ^ 10816 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_633084149 : Nat.Prime 633084149 := by
  apply lucas_primality 633084149 (2 : ZMod 633084149)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (1823, 1), (5107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (1823, 1), (5107, 1)] : List FactorBlock).map factorBlockValue).prod) = 633084149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_1823
      · exact prime_ninetyOneCK_5107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 633084149) ^ 316542074 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 633084149) ^ 37240244 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 633084149) ^ 347276 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 633084149) ^ 123964 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_637670179 : Nat.Prime 637670179 := by
  apply lucas_primality 637670179 (3 : ZMod 637670179)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11808707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11808707, 1)] : List FactorBlock).map factorBlockValue).prod) = 637670179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_11808707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 637670179) ^ 318835089 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 637670179) ^ 212556726 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 637670179) ^ 54 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_656852411 : Nat.Prime 656852411 := by
  apply lucas_primality 656852411 (6 : ZMod 656852411)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (313, 1), (209857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (313, 1), (209857, 1)] : List FactorBlock).map factorBlockValue).prod) = 656852411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_313
      · exact prime_ninetyOneCK_209857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 656852411) ^ 328426205 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 656852411) ^ 131370482 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 656852411) ^ 2098570 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 656852411) ^ 3130 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_660275071 : Nat.Prime 660275071 := by
  apply lucas_primality 660275071 (7 : ZMod 660275071)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (41, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (41, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 660275071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_41
      · exact prime_ninetyOneCK_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 660275071) ^ 330137535 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 660275071) ^ 220091690 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 660275071) ^ 132055014 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 660275071) ^ 94325010 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 660275071) ^ 50790390 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 660275071) ^ 38839710 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 660275071) ^ 16104270 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 660275071) ^ 1902810 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_702741209 : Nat.Prime 702741209 := by
  apply lucas_primality 702741209 (3 : ZMod 702741209)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 3), (39983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 3), (39983, 1)] : List FactorBlock).map factorBlockValue).prod) = 702741209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_39983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 702741209) ^ 351370604 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 702741209) ^ 54057016 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 702741209) ^ 17576 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_730908757 : Nat.Prime 730908757 := by
  apply lucas_primality 730908757 (5 : ZMod 730908757)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (193, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (193, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 730908757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_59
      · exact prime_ninetyOneCK_193
      · exact prime_ninetyOneCK_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 730908757) ^ 365454378 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 730908757) ^ 243636252 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 730908757) ^ 12388284 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 730908757) ^ 3787092 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 730908757) ^ 409932 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_767495077 : Nat.Prime 767495077 := by
  apply lucas_primality 767495077 (2 : ZMod 767495077)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1193, 1), (53611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1193, 1), (53611, 1)] : List FactorBlock).map factorBlockValue).prod) = 767495077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_1193
      · exact prime_ninetyOneCK_53611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 767495077) ^ 383747538 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 767495077) ^ 255831692 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 767495077) ^ 643332 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 767495077) ^ 14316 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_817741039 : Nat.Prime 817741039 := by
  apply lucas_primality 817741039 (3 : ZMod 817741039)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (131, 1), (3221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (131, 1), (3221, 1)] : List FactorBlock).map factorBlockValue).prod) = 817741039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_131
      · exact prime_ninetyOneCK_3221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817741039) ^ 408870519 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 817741039) ^ 272580346 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 817741039) ^ 48102414 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 817741039) ^ 43039002 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 817741039) ^ 6242298 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 817741039) ^ 253878 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_852018269 : Nat.Prime 852018269 := by
  apply lucas_primality 852018269 (2 : ZMod 852018269)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (213004567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (213004567, 1)] : List FactorBlock).map factorBlockValue).prod) = 852018269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_213004567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 852018269) ^ 426009134 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 852018269) ^ 4 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_894909319 : Nat.Prime 894909319 := by
  apply lucas_primality 894909319 (6 : ZMod 894909319)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (947, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (947, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) = 894909319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_947
      · exact prime_ninetyOneCK_5431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 894909319) ^ 447454659 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 894909319) ^ 298303106 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 894909319) ^ 30858942 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 894909319) ^ 944994 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 894909319) ^ 164778 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_927996973 : Nat.Prime 927996973 := by
  apply lucas_primality 927996973 (2 : ZMod 927996973)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11047583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11047583, 1)] : List FactorBlock).map factorBlockValue).prod) = 927996973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_11047583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 927996973) ^ 463998486 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 927996973) ^ 309332324 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 927996973) ^ 132570996 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 927996973) ^ 84 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_952285781 : Nat.Prime 952285781 := by
  apply lucas_primality 952285781 (3 : ZMod 952285781)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47614289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47614289, 1)] : List FactorBlock).map factorBlockValue).prod) = 952285781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_47614289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 952285781) ^ 476142890 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 952285781) ^ 190457156 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 952285781) ^ 20 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_978772519 : Nat.Prime 978772519 := by
  apply lucas_primality 978772519 (3 : ZMod 978772519)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (53, 1), (20117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (53, 1), (20117, 1)] : List FactorBlock).map factorBlockValue).prod) = 978772519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_53
      · exact prime_ninetyOneCK_20117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 978772519) ^ 489386259 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 978772519) ^ 326257506 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 978772519) ^ 57574854 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 978772519) ^ 18467406 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 978772519) ^ 48654 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1175815609 : Nat.Prime 1175815609 := by
  apply lucas_primality 1175815609 (7 : ZMod 1175815609)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (17, 1), (19, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (17, 1), (19, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1175815609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_13789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1175815609) ^ 587907804 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1175815609) ^ 391938536 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1175815609) ^ 106892328 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1175815609) ^ 69165624 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1175815609) ^ 61885032 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1175815609) ^ 85272 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1195894369 : Nat.Prime 1195894369 := by
  apply lucas_primality 1195894369 (7 : ZMod 1195894369)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 5), (113, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 5), (113, 1), (1361, 1)] : List FactorBlock).map factorBlockValue).prod) = 1195894369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_113
      · exact prime_ninetyOneCK_1361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1195894369) ^ 597947184 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1195894369) ^ 398631456 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1195894369) ^ 10583136 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1195894369) ^ 878688 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1255836083 : Nat.Prime 1255836083 := by
  apply lucas_primality 1255836083 (2 : ZMod 1255836083)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (821, 1), (10477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (821, 1), (10477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255836083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_73
      · exact prime_ninetyOneCK_821
      · exact prime_ninetyOneCK_10477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1255836083) ^ 627918041 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1255836083) ^ 17203234 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1255836083) ^ 1529642 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1255836083) ^ 119866 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1337437789 : Nat.Prime 1337437789 := by
  apply lucas_primality 1337437789 (2 : ZMod 1337437789)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (111453149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (111453149, 1)] : List FactorBlock).map factorBlockValue).prod) = 1337437789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_111453149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1337437789) ^ 668718894 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1337437789) ^ 445812596 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1337437789) ^ 12 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1416436831 : Nat.Prime 1416436831 := by
  apply lucas_primality 1416436831 (6 : ZMod 1416436831)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 1), (684269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 1), (684269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1416436831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_684269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1416436831) ^ 708218415 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1416436831) ^ 472145610 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1416436831) ^ 283287366 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1416436831) ^ 61584210 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1416436831) ^ 2070 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1508440883 : Nat.Prime 1508440883 := by
  apply lucas_primality 1508440883 (2 : ZMod 1508440883)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (58016957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (58016957, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508440883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_58016957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1508440883) ^ 754220441 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1508440883) ^ 116033914 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1508440883) ^ 26 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1514938883 : Nat.Prime 1514938883 := by
  apply lucas_primality 1514938883 (2 : ZMod 1514938883)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (383, 1), (1977727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (383, 1), (1977727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514938883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_383
      · exact prime_ninetyOneCK_1977727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1514938883) ^ 757469441 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514938883) ^ 3955454 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514938883) ^ 766 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1789345889 : Nat.Prime 1789345889 := by
  apply lucas_primality 1789345889 (3 : ZMod 1789345889)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (139, 1), (36571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (139, 1), (36571, 1)] : List FactorBlock).map factorBlockValue).prod) = 1789345889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_139
      · exact prime_ninetyOneCK_36571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1789345889) ^ 894672944 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1789345889) ^ 162667808 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1789345889) ^ 12872992 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1789345889) ^ 48928 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1957775189 : Nat.Prime 1957775189 := by
  apply lucas_primality 1957775189 (2 : ZMod 1957775189)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (523, 1), (935839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (523, 1), (935839, 1)] : List FactorBlock).map factorBlockValue).prod) = 1957775189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_523
      · exact prime_ninetyOneCK_935839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1957775189) ^ 978887594 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957775189) ^ 3743356 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957775189) ^ 2092 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2103600437 : Nat.Prime 2103600437 := by
  apply lucas_primality 2103600437 (2 : ZMod 2103600437)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (75128587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (75128587, 1)] : List FactorBlock).map factorBlockValue).prod) = 2103600437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_75128587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2103600437) ^ 1051800218 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2103600437) ^ 300514348 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2103600437) ^ 28 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2119944949 : Nat.Prime 2119944949 := by
  apply lucas_primality 2119944949 (6 : ZMod 2119944949)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (944717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (944717, 1)] : List FactorBlock).map factorBlockValue).prod) = 2119944949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_944717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2119944949) ^ 1059972474 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2119944949) ^ 706648316 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2119944949) ^ 192722268 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2119944949) ^ 124702644 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2119944949) ^ 2244 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2219773681 : Nat.Prime 2219773681 := by
  apply lucas_primality 2219773681 (13 : ZMod 2219773681)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (29, 1), (35437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (29, 1), (35437, 1)] : List FactorBlock).map factorBlockValue).prod) = 2219773681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_35437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2219773681) ^ 1109886840 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 2219773681) ^ 739924560 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 2219773681) ^ 443954736 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 2219773681) ^ 76543920 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 2219773681) ^ 62640 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2329140257 : Nat.Prime 2329140257 := by
  apply lucas_primality 2329140257 (3 : ZMod 2329140257)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (72785633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (72785633, 1)] : List FactorBlock).map factorBlockValue).prod) = 2329140257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_72785633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2329140257) ^ 1164570128 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2329140257) ^ 32 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2432069797 : Nat.Prime 2432069797 := by
  apply lucas_primality 2432069797 (5 : ZMod 2432069797)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (15590191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (15590191, 1)] : List FactorBlock).map factorBlockValue).prod) = 2432069797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_15590191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2432069797) ^ 1216034898 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2432069797) ^ 810689932 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2432069797) ^ 187082292 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2432069797) ^ 156 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2778591583 : Nat.Prime 2778591583 := by
  apply lucas_primality 2778591583 (3 : ZMod 2778591583)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (179, 1), (66337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (179, 1), (66337, 1)] : List FactorBlock).map factorBlockValue).prod) = 2778591583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_179
      · exact prime_ninetyOneCK_66337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2778591583) ^ 1389295791 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2778591583) ^ 926197194 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2778591583) ^ 213737814 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2778591583) ^ 15522858 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2778591583) ^ 41886 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3132173431 : Nat.Prime 3132173431 := by
  apply lucas_primality 3132173431 (7 : ZMod 3132173431)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (787, 1), (44221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (787, 1), (44221, 1)] : List FactorBlock).map factorBlockValue).prod) = 3132173431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_787
      · exact prime_ninetyOneCK_44221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3132173431) ^ 1566086715 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3132173431) ^ 1044057810 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3132173431) ^ 626434686 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3132173431) ^ 3979890 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 3132173431) ^ 70830 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3187831639 : Nat.Prime 3187831639 := by
  apply lucas_primality 3187831639 (3 : ZMod 3187831639)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191, 1), (2781703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191, 1), (2781703, 1)] : List FactorBlock).map factorBlockValue).prod) = 3187831639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_191
      · exact prime_ninetyOneCK_2781703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3187831639) ^ 1593915819 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3187831639) ^ 1062610546 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3187831639) ^ 16690218 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3187831639) ^ 1146 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3832847929 : Nat.Prime 3832847929 := by
  apply lucas_primality 3832847929 (31 : ZMod 3832847929)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (13, 1), (503, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (13, 1), (503, 1), (1163, 1)] : List FactorBlock).map factorBlockValue).prod) = 3832847929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_503
      · exact prime_ninetyOneCK_1163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 3832847929) ^ 1916423964 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (31 : ZMod 3832847929) ^ 1277615976 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (31 : ZMod 3832847929) ^ 547549704 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (31 : ZMod 3832847929) ^ 294834456 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (31 : ZMod 3832847929) ^ 7619976 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (31 : ZMod 3832847929) ^ 3295656 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3940483559 : Nat.Prime 3940483559 := by
  apply lucas_primality 3940483559 (11 : ZMod 3940483559)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (179112889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (179112889, 1)] : List FactorBlock).map factorBlockValue).prod) = 3940483559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_179112889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 3940483559) ^ 1970241779 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 3940483559) ^ 358225778 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 3940483559) ^ 22 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4015133693 : Nat.Prime 4015133693 := by
  apply lucas_primality 4015133693 (2 : ZMod 4015133693)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (281, 1), (3572183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (281, 1), (3572183, 1)] : List FactorBlock).map factorBlockValue).prod) = 4015133693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_281
      · exact prime_ninetyOneCK_3572183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4015133693) ^ 2007566846 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4015133693) ^ 14288732 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4015133693) ^ 1124 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4371501137 : Nat.Prime 4371501137 := by
  apply lucas_primality 4371501137 (3 : ZMod 4371501137)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (457, 1), (597853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (457, 1), (597853, 1)] : List FactorBlock).map factorBlockValue).prod) = 4371501137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_457
      · exact prime_ninetyOneCK_597853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4371501137) ^ 2185750568 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4371501137) ^ 9565648 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4371501137) ^ 7312 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4618695583 : Nat.Prime 4618695583 := by
  apply lucas_primality 4618695583 (3 : ZMod 4618695583)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1103, 1), (232633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1103, 1), (232633, 1)] : List FactorBlock).map factorBlockValue).prod) = 4618695583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_1103
      · exact prime_ninetyOneCK_232633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4618695583) ^ 2309347791 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4618695583) ^ 1539565194 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4618695583) ^ 4187394 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4618695583) ^ 19854 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4684020233 : Nat.Prime 4684020233 := by
  apply lucas_primality 4684020233 (3 : ZMod 4684020233)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (585502529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (585502529, 1)] : List FactorBlock).map factorBlockValue).prod) = 4684020233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_585502529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4684020233) ^ 2342010116 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4684020233) ^ 8 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_5007398047 : Nat.Prime 5007398047 := by
  apply lucas_primality 5007398047 (3 : ZMod 5007398047)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (119223763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (119223763, 1)] : List FactorBlock).map factorBlockValue).prod) = 5007398047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_119223763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5007398047) ^ 2503699023 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5007398047) ^ 1669132682 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5007398047) ^ 715342578 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5007398047) ^ 42 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_5837533553 : Nat.Prime 5837533553 := by
  apply lucas_primality 5837533553 (3 : ZMod 5837533553)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (373, 1), (51481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (373, 1), (51481, 1)] : List FactorBlock).map factorBlockValue).prod) = 5837533553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_373
      · exact prime_ninetyOneCK_51481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5837533553) ^ 2918766776 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5837533553) ^ 307238608 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5837533553) ^ 15650224 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5837533553) ^ 113392 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_6438090829 : Nat.Prime 6438090829 := by
  apply lucas_primality 6438090829 (2 : ZMod 6438090829)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (29, 1), (109469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (29, 1), (109469, 1)] : List FactorBlock).map factorBlockValue).prod) = 6438090829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_109469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6438090829) ^ 3219045414 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6438090829) ^ 2146030276 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6438090829) ^ 495237756 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6438090829) ^ 222003132 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6438090829) ^ 58812 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_7652042149 : Nat.Prime 7652042149 := by
  apply lucas_primality 7652042149 (2 : ZMod 7652042149)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (637670179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (637670179, 1)] : List FactorBlock).map factorBlockValue).prod) = 7652042149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_637670179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7652042149) ^ 3826021074 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7652042149) ^ 2550680716 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7652042149) ^ 12 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_8519422757 : Nat.Prime 8519422757 := by
  apply lucas_primality 8519422757 (2 : ZMod 8519422757)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (163835053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (163835053, 1)] : List FactorBlock).map factorBlockValue).prod) = 8519422757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_163835053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8519422757) ^ 4259711378 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8519422757) ^ 655340212 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8519422757) ^ 52 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_13034063689 : Nat.Prime 13034063689 := by
  apply lucas_primality 13034063689 (21 : ZMod 13034063689)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (29, 1), (47, 1), (67, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (29, 1), (47, 1), (67, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 13034063689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_47
      · exact prime_ninetyOneCK_67
      · exact prime_ninetyOneCK_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 13034063689) ^ 6517031844 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 13034063689) ^ 4344687896 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 13034063689) ^ 686003352 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 13034063689) ^ 449450472 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 13034063689) ^ 277320504 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 13034063689) ^ 194538264 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 13034063689) ^ 41642376 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_14592418783 : Nat.Prime 14592418783 := by
  apply lucas_primality 14592418783 (19 : ZMod 14592418783)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2432069797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2432069797, 1)] : List FactorBlock).map factorBlockValue).prod) = 14592418783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_2432069797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 14592418783) ^ 7296209391 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 14592418783) ^ 4864139594 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 14592418783) ^ 6 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_16323835301 : Nat.Prime 16323835301 := by
  apply lucas_primality 16323835301 (2 : ZMod 16323835301)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (9613, 1), (16981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (9613, 1), (16981, 1)] : List FactorBlock).map factorBlockValue).prod) = 16323835301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_9613
      · exact prime_ninetyOneCK_16981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16323835301) ^ 8161917650 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16323835301) ^ 3264767060 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16323835301) ^ 1698100 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16323835301) ^ 961300 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_22325601481 : Nat.Prime 22325601481 := by
  apply lucas_primality 22325601481 (11 : ZMod 22325601481)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 2), (13, 1), (97, 1), (3011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 2), (13, 1), (97, 1), (3011, 1)] : List FactorBlock).map factorBlockValue).prod) = 22325601481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_97
      · exact prime_ninetyOneCK_3011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22325601481) ^ 11162800740 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22325601481) ^ 7441867160 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22325601481) ^ 4465120296 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22325601481) ^ 3189371640 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22325601481) ^ 1717353960 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22325601481) ^ 230160840 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22325601481) ^ 7414680 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_22736545831 : Nat.Prime 22736545831 := by
  apply lucas_primality 22736545831 (3 : ZMod 22736545831)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (84209429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (84209429, 1)] : List FactorBlock).map factorBlockValue).prod) = 22736545831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_84209429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22736545831) ^ 11368272915 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 22736545831) ^ 7578848610 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 22736545831) ^ 4547309166 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 22736545831) ^ 270 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_23894043391 : Nat.Prime 23894043391 := by
  apply lucas_primality 23894043391 (3 : ZMod 23894043391)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (7, 1), (4214117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (7, 1), (4214117, 1)] : List FactorBlock).map factorBlockValue).prod) = 23894043391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_4214117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23894043391) ^ 11947021695 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23894043391) ^ 7964681130 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23894043391) ^ 4778808678 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23894043391) ^ 3413434770 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 23894043391) ^ 5670 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_33485042333 : Nat.Prime 33485042333 := by
  apply lucas_primality 33485042333 (2 : ZMod 33485042333)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1195894369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1195894369, 1)] : List FactorBlock).map factorBlockValue).prod) = 33485042333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_1195894369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33485042333) ^ 16742521166 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33485042333) ^ 4783577476 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33485042333) ^ 28 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_41561192209 : Nat.Prime 41561192209 := by
  apply lucas_primality 41561192209 (7 : ZMod 41561192209)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (557, 1), (773, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (557, 1), (773, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 41561192209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_557
      · exact prime_ninetyOneCK_773
      · exact prime_ninetyOneCK_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 41561192209) ^ 20780596104 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 41561192209) ^ 13853730736 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 41561192209) ^ 74616144 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 41561192209) ^ 53766096 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 41561192209) ^ 20666928 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_58763755657 : Nat.Prime 58763755657 := by
  apply lucas_primality 58763755657 (5 : ZMod 58763755657)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (503, 1), (1622591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (503, 1), (1622591, 1)] : List FactorBlock).map factorBlockValue).prod) = 58763755657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_503
      · exact prime_ninetyOneCK_1622591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 58763755657) ^ 29381877828 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 58763755657) ^ 19587918552 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 58763755657) ^ 116826552 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 58763755657) ^ 36216 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_65289018161 : Nat.Prime 65289018161 := by
  apply lucas_primality 65289018161 (3 : ZMod 65289018161)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (31, 1), (449, 1), (3449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (31, 1), (449, 1), (3449, 1)] : List FactorBlock).map factorBlockValue).prod) = 65289018161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_31
      · exact prime_ninetyOneCK_449
      · exact prime_ninetyOneCK_3449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65289018161) ^ 32644509080 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65289018161) ^ 13057803632 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65289018161) ^ 3840530480 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65289018161) ^ 2106097360 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65289018161) ^ 145409840 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65289018161) ^ 18929840 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_73402975543 : Nat.Prime 73402975543 := by
  apply lucas_primality 73402975543 (3 : ZMod 73402975543)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (241, 1), (3904829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (241, 1), (3904829, 1)] : List FactorBlock).map factorBlockValue).prod) = 73402975543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_241
      · exact prime_ninetyOneCK_3904829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 73402975543) ^ 36701487771 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 73402975543) ^ 24467658514 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 73402975543) ^ 5646382734 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 73402975543) ^ 304576662 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 73402975543) ^ 18798 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_81783376469 : Nat.Prime 81783376469 := by
  apply lucas_primality 81783376469 (2 : ZMod 81783376469)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (283, 1), (557, 1), (129707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (283, 1), (557, 1), (129707, 1)] : List FactorBlock).map factorBlockValue).prod) = 81783376469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_283
      · exact prime_ninetyOneCK_557
      · exact prime_ninetyOneCK_129707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 81783376469) ^ 40891688234 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 81783376469) ^ 288987196 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 81783376469) ^ 146828324 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 81783376469) ^ 630524 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_87566562373 : Nat.Prime 87566562373 := by
  apply lucas_primality 87566562373 (6 : ZMod 87566562373)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1549, 1), (4710919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1549, 1), (4710919, 1)] : List FactorBlock).map factorBlockValue).prod) = 87566562373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_1549
      · exact prime_ninetyOneCK_4710919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 87566562373) ^ 43783281186 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 87566562373) ^ 29188854124 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 87566562373) ^ 56531028 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 87566562373) ^ 18588 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_95215279351 : Nat.Prime 95215279351 := by
  apply lucas_primality 95215279351 (3 : ZMod 95215279351)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (349, 1), (379, 1), (4799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (349, 1), (379, 1), (4799, 1)] : List FactorBlock).map factorBlockValue).prod) = 95215279351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_349
      · exact prime_ninetyOneCK_379
      · exact prime_ninetyOneCK_4799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95215279351) ^ 47607639675 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 95215279351) ^ 31738426450 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 95215279351) ^ 19043055870 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 95215279351) ^ 272823150 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 95215279351) ^ 251227650 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 95215279351) ^ 19840650 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_95547942913 : Nat.Prime 95547942913 := by
  apply lucas_primality 95547942913 (7 : ZMod 95547942913)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 1), (41, 1), (43, 1), (8821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 1), (41, 1), (43, 1), (8821, 1)] : List FactorBlock).map factorBlockValue).prod) = 95547942913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_41
      · exact prime_ninetyOneCK_43
      · exact prime_ninetyOneCK_8821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 95547942913) ^ 47773971456 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 95547942913) ^ 31849314304 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 95547942913) ^ 2330437632 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 95547942913) ^ 2222045184 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 95547942913) ^ 10831872 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_102468976117 : Nat.Prime 102468976117 := by
  apply lucas_primality 102468976117 (2 : ZMod 102468976117)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (656852411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (656852411, 1)] : List FactorBlock).map factorBlockValue).prod) = 102468976117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_656852411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102468976117) ^ 51234488058 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 102468976117) ^ 34156325372 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 102468976117) ^ 7882228932 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 102468976117) ^ 156 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_106371492971 : Nat.Prime 106371492971 := by
  apply lucas_primality 106371492971 (2 : ZMod 106371492971)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (277, 1), (2021119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (277, 1), (2021119, 1)] : List FactorBlock).map factorBlockValue).prod) = 106371492971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_277
      · exact prime_ninetyOneCK_2021119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106371492971) ^ 53185746485 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106371492971) ^ 21274298594 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106371492971) ^ 5598499630 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106371492971) ^ 384012610 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 106371492971) ^ 52630 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_174718218797 : Nat.Prime 174718218797 := by
  apply lucas_primality 174718218797 (2 : ZMod 174718218797)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (523, 1), (7592483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (523, 1), (7592483, 1)] : List FactorBlock).map factorBlockValue).prod) = 174718218797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_523
      · exact prime_ninetyOneCK_7592483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 174718218797) ^ 87359109398 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 174718218797) ^ 15883474436 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 174718218797) ^ 334069252 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 174718218797) ^ 23012 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_178784338679 : Nat.Prime 178784338679 := by
  apply lucas_primality 178784338679 (7 : ZMod 178784338679)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (61, 1), (191, 1), (63409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (61, 1), (191, 1), (63409, 1)] : List FactorBlock).map factorBlockValue).prod) = 178784338679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_61
      · exact prime_ninetyOneCK_191
      · exact prime_ninetyOneCK_63409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 178784338679) ^ 89392169339 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 178784338679) ^ 16253121698 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 178784338679) ^ 2930890798 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 178784338679) ^ 936043658 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 178784338679) ^ 2819542 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_209854711093 : Nat.Prime 209854711093 := by
  apply lucas_primality 209854711093 (2 : ZMod 209854711093)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (29, 1), (79, 1), (601, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (29, 1), (79, 1), (601, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 209854711093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_79
      · exact prime_ninetyOneCK_601
      · exact prime_ninetyOneCK_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 209854711093) ^ 104927355546 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 209854711093) ^ 69951570364 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 209854711093) ^ 16142670084 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 209854711093) ^ 7236369348 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 209854711093) ^ 2656388748 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 209854711093) ^ 349175892 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 209854711093) ^ 214794996 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_286728520693 : Nat.Prime 286728520693 := by
  apply lucas_primality 286728520693 (2 : ZMod 286728520693)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23894043391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23894043391, 1)] : List FactorBlock).map factorBlockValue).prod) = 286728520693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_23894043391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 286728520693) ^ 143364260346 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 286728520693) ^ 95576173564 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 286728520693) ^ 12 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_319791748079 : Nat.Prime 319791748079 := by
  apply lucas_primality 319791748079 (11 : ZMod 319791748079)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (181, 1), (2309, 1), (34781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (181, 1), (2309, 1), (34781, 1)] : List FactorBlock).map factorBlockValue).prod) = 319791748079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_181
      · exact prime_ninetyOneCK_2309
      · exact prime_ninetyOneCK_34781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 319791748079) ^ 159895874039 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 319791748079) ^ 29071977098 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 319791748079) ^ 1766805238 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 319791748079) ^ 138497942 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 319791748079) ^ 9194438 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_346617497243 : Nat.Prime 346617497243 := by
  apply lucas_primality 346617497243 (2 : ZMod 346617497243)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (4684020233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (4684020233, 1)] : List FactorBlock).map factorBlockValue).prod) = 346617497243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_37
      · exact prime_ninetyOneCK_4684020233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 346617497243) ^ 173308748621 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 346617497243) ^ 9368040466 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 346617497243) ^ 74 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_426567598439 : Nat.Prime 426567598439 := by
  apply lucas_primality 426567598439 (11 : ZMod 426567598439)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (967, 1), (1607, 1), (137251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (967, 1), (1607, 1), (137251, 1)] : List FactorBlock).map factorBlockValue).prod) = 426567598439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_967
      · exact prime_ninetyOneCK_1607
      · exact prime_ninetyOneCK_137251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 426567598439) ^ 213283799219 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 426567598439) ^ 441124714 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 426567598439) ^ 265443434 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 426567598439) ^ 3107938 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_482181259793 : Nat.Prime 482181259793 := by
  apply lucas_primality 482181259793 (3 : ZMod 482181259793)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1187, 1), (25388651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1187, 1), (25388651, 1)] : List FactorBlock).map factorBlockValue).prod) = 482181259793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1187
      · exact prime_ninetyOneCK_25388651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 482181259793) ^ 241090629896 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 482181259793) ^ 406218416 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 482181259793) ^ 18992 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_525399374239 : Nat.Prime 525399374239 := by
  apply lucas_primality 525399374239 (3 : ZMod 525399374239)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (87566562373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (87566562373, 1)] : List FactorBlock).map factorBlockValue).prod) = 525399374239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_87566562373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 525399374239) ^ 262699687119 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 525399374239) ^ 175133124746 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 525399374239) ^ 6 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_562271441233 : Nat.Prime 562271441233 := by
  apply lucas_primality 562271441233 (5 : ZMod 562271441233)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (353, 1), (379, 1), (87557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (353, 1), (379, 1), (87557, 1)] : List FactorBlock).map factorBlockValue).prod) = 562271441233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_353
      · exact prime_ninetyOneCK_379
      · exact prime_ninetyOneCK_87557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 562271441233) ^ 281135720616 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 562271441233) ^ 187423813744 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 562271441233) ^ 1592836944 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 562271441233) ^ 1483565808 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 562271441233) ^ 6421776 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_687918475733 : Nat.Prime 687918475733 := by
  apply lucas_primality 687918475733 (2 : ZMod 687918475733)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (37, 1), (149938639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (37, 1), (149938639, 1)] : List FactorBlock).map factorBlockValue).prod) = 687918475733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_31
      · exact prime_ninetyOneCK_37
      · exact prime_ninetyOneCK_149938639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 687918475733) ^ 343959237866 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 687918475733) ^ 22190918572 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 687918475733) ^ 18592391236 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 687918475733) ^ 4588 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_801643059109 : Nat.Prime 801643059109 := by
  apply lucas_primality 801643059109 (2 : ZMod 801643059109)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (9967, 1), (2234159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (9967, 1), (2234159, 1)] : List FactorBlock).map factorBlockValue).prod) = 801643059109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_9967
      · exact prime_ninetyOneCK_2234159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 801643059109) ^ 400821529554 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 801643059109) ^ 267214353036 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 801643059109) ^ 80429724 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 801643059109) ^ 358812 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_850055280667 : Nat.Prime 850055280667 := by
  apply lucas_primality 850055280667 (2 : ZMod 850055280667)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (41, 1), (293, 1), (20023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (41, 1), (293, 1), (20023, 1)] : List FactorBlock).map factorBlockValue).prod) = 850055280667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_31
      · exact prime_ninetyOneCK_41
      · exact prime_ninetyOneCK_293
      · exact prime_ninetyOneCK_20023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 850055280667) ^ 425027640333 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 850055280667) ^ 283351760222 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 850055280667) ^ 44739751614 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 850055280667) ^ 27421138086 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 850055280667) ^ 20733055626 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 850055280667) ^ 2901212562 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 850055280667) ^ 42453942 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1259128266559 : Nat.Prime 1259128266559 := by
  apply lucas_primality 1259128266559 (3 : ZMod 1259128266559)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (209854711093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (209854711093, 1)] : List FactorBlock).map factorBlockValue).prod) = 1259128266559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_209854711093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1259128266559) ^ 629564133279 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1259128266559) ^ 419709422186 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1259128266559) ^ 6 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1270556105873 : Nat.Prime 1270556105873 := by
  apply lucas_primality 1270556105873 (3 : ZMod 1270556105873)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (113, 1), (702741209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (113, 1), (702741209, 1)] : List FactorBlock).map factorBlockValue).prod) = 1270556105873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_113
      · exact prime_ninetyOneCK_702741209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1270556105873) ^ 635278052936 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1270556105873) ^ 11243859344 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1270556105873) ^ 1808 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1511697906673 : Nat.Prime 1511697906673 := by
  apply lucas_primality 1511697906673 (5 : ZMod 1511697906673)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (433, 1), (72733733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (433, 1), (72733733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1511697906673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_433
      · exact prime_ninetyOneCK_72733733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1511697906673) ^ 755848953336 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511697906673) ^ 503899302224 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511697906673) ^ 3491219184 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1511697906673) ^ 20784 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1792890151837 : Nat.Prime 1792890151837 := by
  apply lucas_primality 1792890151837 (13 : ZMod 1792890151837)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (927996973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (927996973, 1)] : List FactorBlock).map factorBlockValue).prod) = 1792890151837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_927996973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1792890151837) ^ 896445075918 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1792890151837) ^ 597630050612 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1792890151837) ^ 256127164548 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1792890151837) ^ 77951745732 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1792890151837) ^ 1932 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1997796312901 : Nat.Prime 1997796312901 := by
  apply lucas_primality 1997796312901 (2 : ZMod 1997796312901)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (2219773681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (2219773681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1997796312901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_2219773681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1997796312901) ^ 998898156450 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1997796312901) ^ 665932104300 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1997796312901) ^ 399559262580 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1997796312901) ^ 900 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2088235989473 : Nat.Prime 2088235989473 := by
  apply lucas_primality 2088235989473 (3 : ZMod 2088235989473)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (1447, 1), (1555117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (1447, 1), (1555117, 1)] : List FactorBlock).map factorBlockValue).prod) = 2088235989473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_1447
      · exact prime_ninetyOneCK_1555117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2088235989473) ^ 1044117994736 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2088235989473) ^ 72008137568 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2088235989473) ^ 1443148576 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2088235989473) ^ 1342816 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2349280869841 : Nat.Prime 2349280869841 := by
  apply lucas_primality 2349280869841 (14 : ZMod 2349280869841)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (313, 1), (10424569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (313, 1), (10424569, 1)] : List FactorBlock).map factorBlockValue).prod) = 2349280869841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_313
      · exact prime_ninetyOneCK_10424569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2349280869841) ^ 1174640434920 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2349280869841) ^ 783093623280 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2349280869841) ^ 469856173968 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2349280869841) ^ 7505689680 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 2349280869841) ^ 225360 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2501234868091 : Nat.Prime 2501234868091 := by
  apply lucas_primality 2501234868091 (7 : ZMod 2501234868091)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (41, 1), (10017361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (41, 1), (10017361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2501234868091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_41
      · exact prime_ninetyOneCK_10017361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2501234868091) ^ 1250617434045 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2501234868091) ^ 833744956030 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2501234868091) ^ 500246973618 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2501234868091) ^ 357319266870 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2501234868091) ^ 86249478210 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2501234868091) ^ 61005728490 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2501234868091) ^ 249690 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2746166290247 : Nat.Prime 2746166290247 := by
  apply lucas_primality 2746166290247 (5 : ZMod 2746166290247)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (23159, 1), (666173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (23159, 1), (666173, 1)] : List FactorBlock).map factorBlockValue).prod) = 2746166290247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_89
      · exact prime_ninetyOneCK_23159
      · exact prime_ninetyOneCK_666173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2746166290247) ^ 1373083145123 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2746166290247) ^ 30855801014 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2746166290247) ^ 118578794 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2746166290247) ^ 4122302 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2851643202613 : Nat.Prime 2851643202613 := by
  apply lucas_primality 2851643202613 (6 : ZMod 2851643202613)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (29, 1), (797, 1), (541133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (29, 1), (797, 1), (541133, 1)] : List FactorBlock).map factorBlockValue).prod) = 2851643202613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_797
      · exact prime_ninetyOneCK_541133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2851643202613) ^ 1425821601306 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2851643202613) ^ 950547734204 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2851643202613) ^ 150086484348 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2851643202613) ^ 98332524228 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2851643202613) ^ 3577971396 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 2851643202613) ^ 5269764 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2915625496517 : Nat.Prime 2915625496517 := by
  apply lucas_primality 2915625496517 (2 : ZMod 2915625496517)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (5839, 1), (7343183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (5839, 1), (7343183, 1)] : List FactorBlock).map factorBlockValue).prod) = 2915625496517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_5839
      · exact prime_ninetyOneCK_7343183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2915625496517) ^ 1457812748258 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2915625496517) ^ 171507382148 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2915625496517) ^ 499336444 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2915625496517) ^ 397052 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3602518855597 : Nat.Prime 3602518855597 := by
  apply lucas_primality 3602518855597 (5 : ZMod 3602518855597)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 1), (2053, 1), (1680803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 1), (2053, 1), (1680803, 1)] : List FactorBlock).map factorBlockValue).prod) = 3602518855597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_2053
      · exact prime_ninetyOneCK_1680803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3602518855597) ^ 1801259427798 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3602518855597) ^ 1200839618532 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3602518855597) ^ 124224788124 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3602518855597) ^ 1754758332 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3602518855597) ^ 2143332 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3939401153393 : Nat.Prime 3939401153393 := by
  apply lucas_primality 3939401153393 (3 : ZMod 3939401153393)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (317, 1), (569, 1), (1365019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (317, 1), (569, 1), (1365019, 1)] : List FactorBlock).map factorBlockValue).prod) = 3939401153393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_317
      · exact prime_ninetyOneCK_569
      · exact prime_ninetyOneCK_1365019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3939401153393) ^ 1969700576696 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3939401153393) ^ 12427132976 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3939401153393) ^ 6923376368 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3939401153393) ^ 2885968 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4464177524669 : Nat.Prime 4464177524669 := by
  apply lucas_primality 4464177524669 (2 : ZMod 4464177524669)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (8519422757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (8519422757, 1)] : List FactorBlock).map factorBlockValue).prod) = 4464177524669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_131
      · exact prime_ninetyOneCK_8519422757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4464177524669) ^ 2232088762334 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4464177524669) ^ 34077691028 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4464177524669) ^ 524 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4554130514951 : Nat.Prime 4554130514951 := by
  apply lucas_primality 4554130514951 (19 : ZMod 4554130514951)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1879, 1), (48473981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1879, 1), (48473981, 1)] : List FactorBlock).map factorBlockValue).prod) = 4554130514951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_1879
      · exact prime_ninetyOneCK_48473981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 4554130514951) ^ 2277065257475 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 4554130514951) ^ 910826102990 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 4554130514951) ^ 2423699050 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (19 : ZMod 4554130514951) ^ 93950 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_5118811181269 : Nat.Prime 5118811181269 := by
  apply lucas_primality 5118811181269 (2 : ZMod 5118811181269)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (426567598439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (426567598439, 1)] : List FactorBlock).map factorBlockValue).prod) = 5118811181269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_426567598439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5118811181269) ^ 2559405590634 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118811181269) ^ 1706270393756 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5118811181269) ^ 12 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_6036069407581 : Nat.Prime 6036069407581 := by
  apply lucas_primality 6036069407581 (2 : ZMod 6036069407581)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (163, 1), (205728337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (163, 1), (205728337, 1)] : List FactorBlock).map factorBlockValue).prod) = 6036069407581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_163
      · exact prime_ninetyOneCK_205728337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6036069407581) ^ 3018034703790 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6036069407581) ^ 2012023135860 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6036069407581) ^ 1207213881516 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6036069407581) ^ 37031100660 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6036069407581) ^ 29340 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_7171560607349 : Nat.Prime 7171560607349 := by
  apply lucas_primality 7171560607349 (2 : ZMod 7171560607349)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1792890151837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1792890151837, 1)] : List FactorBlock).map factorBlockValue).prod) = 7171560607349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1792890151837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7171560607349) ^ 3585780303674 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7171560607349) ^ 4 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_10650401557979 : Nat.Prime 10650401557979 := by
  apply lucas_primality 10650401557979 (6 : ZMod 10650401557979)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (41, 1), (173, 1), (383, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (41, 1), (173, 1), (383, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) = 10650401557979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_41
      · exact prime_ninetyOneCK_173
      · exact prime_ninetyOneCK_383
      · exact prime_ninetyOneCK_1657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10650401557979) ^ 5325200778989 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 10650401557979) ^ 1521485936854 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 10650401557979) ^ 819261658306 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 10650401557979) ^ 259765891658 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 10650401557979) ^ 61563014786 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 10650401557979) ^ 27807836966 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 10650401557979) ^ 6427520554 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_10895963829437 : Nat.Prime 10895963829437 := by
  apply lucas_primality 10895963829437 (2 : ZMod 10895963829437)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (479, 1), (8513, 1), (13633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (479, 1), (8513, 1), (13633, 1)] : List FactorBlock).map factorBlockValue).prod) = 10895963829437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_479
      · exact prime_ninetyOneCK_8513
      · exact prime_ninetyOneCK_13633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10895963829437) ^ 5447981914718 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10895963829437) ^ 1556566261348 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10895963829437) ^ 22747314884 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10895963829437) ^ 1279920572 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10895963829437) ^ 799234492 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_20929468621379 : Nat.Prime 20929468621379 := by
  apply lucas_primality 20929468621379 (2 : ZMod 20929468621379)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (271, 1), (281, 1), (600091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (271, 1), (281, 1), (600091, 1)] : List FactorBlock).map factorBlockValue).prod) = 20929468621379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_229
      · exact prime_ninetyOneCK_271
      · exact prime_ninetyOneCK_281
      · exact prime_ninetyOneCK_600091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20929468621379) ^ 10464734310689 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20929468621379) ^ 91395059482 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20929468621379) ^ 77230511518 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20929468621379) ^ 74482094738 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 20929468621379) ^ 34877158 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_21969330321977 : Nat.Prime 21969330321977 := by
  apply lucas_primality 21969330321977 (3 : ZMod 21969330321977)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2746166290247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2746166290247, 1)] : List FactorBlock).map factorBlockValue).prod) = 21969330321977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_2746166290247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 21969330321977) ^ 10984665160988 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 21969330321977) ^ 8 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_34840009591591 : Nat.Prime 34840009591591 := by
  apply lucas_primality 34840009591591 (3 : ZMod 34840009591591)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (251, 1), (787, 1), (119981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (251, 1), (787, 1), (119981, 1)] : List FactorBlock).map factorBlockValue).prod) = 34840009591591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_251
      · exact prime_ninetyOneCK_787
      · exact prime_ninetyOneCK_119981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34840009591591) ^ 17420004795795 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34840009591591) ^ 11613336530530 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34840009591591) ^ 6968001918318 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34840009591591) ^ 4977144227370 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34840009591591) ^ 138804819090 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34840009591591) ^ 44269389570 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34840009591591) ^ 290379390 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_58431345368959 : Nat.Prime 58431345368959 := by
  apply lucas_primality 58431345368959 (3 : ZMod 58431345368959)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (163, 1), (571, 1), (2887, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (163, 1), (571, 1), (2887, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) = 58431345368959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_163
      · exact prime_ninetyOneCK_571
      · exact prime_ninetyOneCK_2887
      · exact prime_ninetyOneCK_4027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 58431345368959) ^ 29215672684479 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 58431345368959) ^ 19477115122986 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 58431345368959) ^ 358474511466 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 58431345368959) ^ 102331603098 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 58431345368959) ^ 20239468434 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 58431345368959) ^ 14509894554 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_84171504309469 : Nat.Prime 84171504309469 := by
  apply lucas_primality 84171504309469 (2 : ZMod 84171504309469)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (463, 1), (1033, 1), (3491, 1), (4201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (463, 1), (1033, 1), (3491, 1), (4201, 1)] : List FactorBlock).map factorBlockValue).prod) = 84171504309469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_463
      · exact prime_ninetyOneCK_1033
      · exact prime_ninetyOneCK_3491
      · exact prime_ninetyOneCK_4201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84171504309469) ^ 42085752154734 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84171504309469) ^ 28057168103156 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84171504309469) ^ 181795905636 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84171504309469) ^ 81482579196 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84171504309469) ^ 24111000948 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 84171504309469) ^ 20036063868 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_85386763552583 : Nat.Prime 85386763552583 := by
  apply lucas_primality 85386763552583 (5 : ZMod 85386763552583)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (37, 1), (103, 1), (24247, 1), (24317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (37, 1), (103, 1), (24247, 1), (24317, 1)] : List FactorBlock).map factorBlockValue).prod) = 85386763552583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_37
      · exact prime_ninetyOneCK_103
      · exact prime_ninetyOneCK_24247
      · exact prime_ninetyOneCK_24317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 85386763552583) ^ 42693381776291 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 85386763552583) ^ 4494040186978 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 85386763552583) ^ 2307750366286 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 85386763552583) ^ 828997704394 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 85386763552583) ^ 3521539306 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 85386763552583) ^ 3511402046 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_103945074633473 : Nat.Prime 103945074633473 := by
  apply lucas_primality 103945074633473 (3 : ZMod 103945074633473)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (20641, 1), (19671307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (20641, 1), (19671307, 1)] : List FactorBlock).map factorBlockValue).prod) = 103945074633473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_20641
      · exact prime_ninetyOneCK_19671307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103945074633473) ^ 51972537316736 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 103945074633473) ^ 5035854592 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 103945074633473) ^ 5284096 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_126224547151237 : Nat.Prime 126224547151237 := by
  apply lucas_primality 126224547151237 (2 : ZMod 126224547151237)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (58763755657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (58763755657, 1)] : List FactorBlock).map factorBlockValue).prod) = 126224547151237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_179
      · exact prime_ninetyOneCK_58763755657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 126224547151237) ^ 63112273575618 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 126224547151237) ^ 42074849050412 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 126224547151237) ^ 705165067884 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 126224547151237) ^ 2148 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_133384928306549 : Nat.Prime 133384928306549 := by
  apply lucas_primality 133384928306549 (2 : ZMod 133384928306549)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (349, 1), (95547942913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (349, 1), (95547942913, 1)] : List FactorBlock).map factorBlockValue).prod) = 133384928306549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_349
      · exact prime_ninetyOneCK_95547942913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 133384928306549) ^ 66692464153274 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133384928306549) ^ 382191771652 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133384928306549) ^ 1396 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_140923644553819 : Nat.Prime 140923644553819 := by
  apply lucas_primality 140923644553819 (2 : ZMod 140923644553819)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (359, 1), (8647, 1), (120097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (359, 1), (8647, 1), (120097, 1)] : List FactorBlock).map factorBlockValue).prod) = 140923644553819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_359
      · exact prime_ninetyOneCK_8647
      · exact prime_ninetyOneCK_120097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 140923644553819) ^ 70461822276909 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 140923644553819) ^ 46974548184606 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 140923644553819) ^ 20131949221974 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 140923644553819) ^ 392544970902 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 140923644553819) ^ 16297403094 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 140923644553819) ^ 1173415194 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_194210383200313 : Nat.Prime 194210383200313 := by
  apply lucas_primality 194210383200313 (11 : ZMod 194210383200313)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (239, 1), (2053, 1), (568691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (239, 1), (2053, 1), (568691, 1)] : List FactorBlock).map factorBlockValue).prod) = 194210383200313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_239
      · exact prime_ninetyOneCK_2053
      · exact prime_ninetyOneCK_568691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 194210383200313) ^ 97105191600156 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 194210383200313) ^ 64736794400104 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 194210383200313) ^ 6696909765528 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 194210383200313) ^ 812595745608 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 194210383200313) ^ 94598335704 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 194210383200313) ^ 341504232 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_196431189507907 : Nat.Prime 196431189507907 := by
  apply lucas_primality 196431189507907 (5 : ZMod 196431189507907)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (9949, 1), (106149529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (9949, 1), (106149529, 1)] : List FactorBlock).map factorBlockValue).prod) = 196431189507907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_31
      · exact prime_ninetyOneCK_9949
      · exact prime_ninetyOneCK_106149529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 196431189507907) ^ 98215594753953 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 196431189507907) ^ 65477063169302 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 196431189507907) ^ 6336489984126 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 196431189507907) ^ 19743812394 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 196431189507907) ^ 1850514 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_250712690703341 : Nat.Prime 250712690703341 := by
  apply lucas_primality 250712690703341 (2 : ZMod 250712690703341)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (337, 1), (1957775189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (337, 1), (1957775189, 1)] : List FactorBlock).map factorBlockValue).prod) = 250712690703341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_337
      · exact prime_ninetyOneCK_1957775189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 250712690703341) ^ 125356345351670 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 250712690703341) ^ 50142538140668 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 250712690703341) ^ 13195404773860 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 250712690703341) ^ 743954571820 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 250712690703341) ^ 128060 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_355354582203617 : Nat.Prime 355354582203617 := by
  apply lucas_primality 355354582203617 (3 : ZMod 355354582203617)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (761, 1), (14592418783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (761, 1), (14592418783, 1)] : List FactorBlock).map factorBlockValue).prod) = 355354582203617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_761
      · exact prime_ninetyOneCK_14592418783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 355354582203617) ^ 177677291101808 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 355354582203617) ^ 466957401056 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 355354582203617) ^ 24352 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_367937471391857 : Nat.Prime 367937471391857 := by
  apply lucas_primality 367937471391857 (3 : ZMod 367937471391857)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (61, 1), (167, 1), (23041, 1), (97973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (61, 1), (167, 1), (23041, 1), (97973, 1)] : List FactorBlock).map factorBlockValue).prod) = 367937471391857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_61
      · exact prime_ninetyOneCK_167
      · exact prime_ninetyOneCK_23041
      · exact prime_ninetyOneCK_97973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 367937471391857) ^ 183968735695928 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 367937471391857) ^ 6031761826096 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 367937471391857) ^ 2203218391568 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 367937471391857) ^ 15968815216 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 367937471391857) ^ 3755498672 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_393922399632551 : Nat.Prime 393922399632551 := by
  apply lucas_primality 393922399632551 (22 : ZMod 393922399632551)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (480911, 1), (16382341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (480911, 1), (16382341, 1)] : List FactorBlock).map factorBlockValue).prod) = 393922399632551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_480911
      · exact prime_ninetyOneCK_16382341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 393922399632551) ^ 196961199816275 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (22 : ZMod 393922399632551) ^ 78784479926510 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (22 : ZMod 393922399632551) ^ 819117050 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (22 : ZMod 393922399632551) ^ 24045550 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_437026458252199 : Nat.Prime 437026458252199 := by
  apply lucas_primality 437026458252199 (6 : ZMod 437026458252199)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (693179, 1), (105077827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (693179, 1), (105077827, 1)] : List FactorBlock).map factorBlockValue).prod) = 437026458252199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_693179
      · exact prime_ninetyOneCK_105077827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 437026458252199) ^ 218513229126099 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 437026458252199) ^ 145675486084066 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 437026458252199) ^ 630466962 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 437026458252199) ^ 4159074 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_504898188604949 : Nat.Prime 504898188604949 := by
  apply lucas_primality 504898188604949 (2 : ZMod 504898188604949)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (126224547151237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (126224547151237, 1)] : List FactorBlock).map factorBlockValue).prod) = 504898188604949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_126224547151237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 504898188604949) ^ 252449094302474 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 504898188604949) ^ 4 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_638714131623319 : Nat.Prime 638714131623319 := by
  apply lucas_primality 638714131623319 (3 : ZMod 638714131623319)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (701, 1), (12689, 1), (703981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (701, 1), (12689, 1), (703981, 1)] : List FactorBlock).map factorBlockValue).prod) = 638714131623319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_701
      · exact prime_ninetyOneCK_12689
      · exact prime_ninetyOneCK_703981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 638714131623319) ^ 319357065811659 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 638714131623319) ^ 212904710541106 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 638714131623319) ^ 37571419507254 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 638714131623319) ^ 911147120718 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 638714131623319) ^ 50336049462 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 638714131623319) ^ 907288878 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_649153343668267 : Nat.Prime 649153343668267 := by
  apply lucas_primality 649153343668267 (2 : ZMod 649153343668267)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1571, 1), (7652042149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1571, 1), (7652042149, 1)] : List FactorBlock).map factorBlockValue).prod) = 649153343668267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_1571
      · exact prime_ninetyOneCK_7652042149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 649153343668267) ^ 324576671834133 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 649153343668267) ^ 216384447889422 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 649153343668267) ^ 413210276046 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 649153343668267) ^ 84834 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_693760829891069 : Nat.Prime 693760829891069 := by
  apply lucas_primality 693760829891069 (2 : ZMod 693760829891069)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6043, 1), (9109, 1), (3150841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6043, 1), (9109, 1), (3150841, 1)] : List FactorBlock).map factorBlockValue).prod) = 693760829891069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_6043
      · exact prime_ninetyOneCK_9109
      · exact prime_ninetyOneCK_3150841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 693760829891069) ^ 346880414945534 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 693760829891069) ^ 114804042676 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 693760829891069) ^ 76162128652 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 693760829891069) ^ 220182748 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_790895891591173 : Nat.Prime 790895891591173 := by
  apply lucas_primality 790895891591173 (2 : ZMod 790895891591173)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (21969330321977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (21969330321977, 1)] : List FactorBlock).map factorBlockValue).prod) = 790895891591173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_21969330321977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 790895891591173) ^ 395447945795586 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 790895891591173) ^ 263631963863724 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 790895891591173) ^ 36 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_837394782914189 : Nat.Prime 837394782914189 := by
  apply lucas_primality 837394782914189 (2 : ZMod 837394782914189)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (179, 1), (152417, 1), (333623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (179, 1), (152417, 1), (333623, 1)] : List FactorBlock).map factorBlockValue).prod) = 837394782914189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_179
      · exact prime_ninetyOneCK_152417
      · exact prime_ninetyOneCK_333623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 837394782914189) ^ 418697391457094 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 837394782914189) ^ 36408468822356 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 837394782914189) ^ 4678183144772 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 837394782914189) ^ 5494103564 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 837394782914189) ^ 2510003156 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_844119026830907 : Nat.Prime 844119026830907 := by
  apply lucas_primality 844119026830907 (2 : ZMod 844119026830907)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (4253, 1), (5837533553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (4253, 1), (5837533553, 1)] : List FactorBlock).map factorBlockValue).prod) = 844119026830907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_4253
      · exact prime_ninetyOneCK_5837533553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 844119026830907) ^ 422059513415453 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 844119026830907) ^ 49654060401818 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 844119026830907) ^ 198476140802 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 844119026830907) ^ 144602 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_937052889331583 : Nat.Prime 937052889331583 := by
  apply lucas_primality 937052889331583 (5 : ZMod 937052889331583)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (10895963829437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (10895963829437, 1)] : List FactorBlock).map factorBlockValue).prod) = 937052889331583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_43
      · exact prime_ninetyOneCK_10895963829437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 937052889331583) ^ 468526444665791 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 937052889331583) ^ 21791927658874 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 937052889331583) ^ 86 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1001396690703517 : Nat.Prime 1001396690703517 := by
  apply lucas_primality 1001396690703517 (2 : ZMod 1001396690703517)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (149, 1), (313, 1), (1789345889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (149, 1), (313, 1), (1789345889, 1)] : List FactorBlock).map factorBlockValue).prod) = 1001396690703517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_149
      · exact prime_ninetyOneCK_313
      · exact prime_ninetyOneCK_1789345889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1001396690703517) ^ 500698345351758 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001396690703517) ^ 333798896901172 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001396690703517) ^ 6720783159084 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001396690703517) ^ 3199350449532 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001396690703517) ^ 559644 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1145131167897713 : Nat.Prime 1145131167897713 := by
  apply lucas_primality 1145131167897713 (3 : ZMod 1145131167897713)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103, 1), (27739, 1), (25049971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103, 1), (27739, 1), (25049971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1145131167897713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_103
      · exact prime_ninetyOneCK_27739
      · exact prime_ninetyOneCK_25049971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1145131167897713) ^ 572565583948856 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1145131167897713) ^ 11117778329104 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1145131167897713) ^ 41282352208 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1145131167897713) ^ 45713872 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1255768117282741 : Nat.Prime 1255768117282741 := by
  apply lucas_primality 1255768117282741 (2 : ZMod 1255768117282741)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (20929468621379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (20929468621379, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255768117282741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_20929468621379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1255768117282741) ^ 627884058641370 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1255768117282741) ^ 418589372427580 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1255768117282741) ^ 251153623456548 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1255768117282741) ^ 60 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1364396486603519 : Nat.Prime 1364396486603519 := by
  apply lucas_primality 1364396486603519 (13 : ZMod 1364396486603519)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (37, 1), (801643059109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (37, 1), (801643059109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1364396486603519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_37
      · exact prime_ninetyOneCK_801643059109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1364396486603519) ^ 682198243301759 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1364396486603519) ^ 59321586374066 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1364396486603519) ^ 36875580719014 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1364396486603519) ^ 1702 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1691083734645829 : Nat.Prime 1691083734645829 := by
  apply lucas_primality 1691083734645829 (6 : ZMod 1691083734645829)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (140923644553819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (140923644553819, 1)] : List FactorBlock).map factorBlockValue).prod) = 1691083734645829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_140923644553819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1691083734645829) ^ 845541867322914 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1691083734645829) ^ 563694578215276 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1691083734645829) ^ 12 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2161493025619247 : Nat.Prime 2161493025619247 := by
  apply lucas_primality 2161493025619247 (10 : ZMod 2161493025619247)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (17, 1), (525399374239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (17, 1), (525399374239, 1)] : List FactorBlock).map factorBlockValue).prod) = 2161493025619247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_525399374239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2161493025619247) ^ 1080746512809623 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2161493025619247) ^ 196499365965386 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2161493025619247) ^ 127146648565838 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 2161493025619247) ^ 4114 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2828314718354221 : Nat.Prime 2828314718354221 := by
  apply lucas_primality 2828314718354221 (2 : ZMod 2828314718354221)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2739421, 1), (17207497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2739421, 1), (17207497, 1)] : List FactorBlock).map factorBlockValue).prod) = 2828314718354221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_2739421
      · exact prime_ninetyOneCK_17207497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2828314718354221) ^ 1414157359177110 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2828314718354221) ^ 942771572784740 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2828314718354221) ^ 565662943670844 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2828314718354221) ^ 1032449820 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2828314718354221) ^ 164365260 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3361869038391551 : Nat.Prime 3361869038391551 := by
  apply lucas_primality 3361869038391551 (14 : ZMod 3361869038391551)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31963, 1), (2103600437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31963, 1), (2103600437, 1)] : List FactorBlock).map factorBlockValue).prod) = 3361869038391551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_31963
      · exact prime_ninetyOneCK_2103600437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 3361869038391551) ^ 1680934519195775 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 3361869038391551) ^ 672373807678310 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 3361869038391551) ^ 105180021850 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 3361869038391551) ^ 1598150 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3533072934144599 : Nat.Prime 3533072934144599 := by
  apply lucas_primality 3533072934144599 (17 : ZMod 3533072934144599)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (79, 1), (100847, 1), (897709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (79, 1), (100847, 1), (897709, 1)] : List FactorBlock).map factorBlockValue).prod) = 3533072934144599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_79
      · exact prime_ninetyOneCK_100847
      · exact prime_ninetyOneCK_897709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 3533072934144599) ^ 1766536467072299 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 3533072934144599) ^ 271774841088046 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 3533072934144599) ^ 185951207060242 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 3533072934144599) ^ 44722442204362 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 3533072934144599) ^ 35033991434 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 3533072934144599) ^ 3935655022 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4005586762814069 : Nat.Prime 4005586762814069 := by
  apply lucas_primality 4005586762814069 (2 : ZMod 4005586762814069)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1001396690703517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1001396690703517, 1)] : List FactorBlock).map factorBlockValue).prod) = 4005586762814069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1001396690703517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4005586762814069) ^ 2002793381407034 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 4005586762814069) ^ 4 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4813236448931849 : Nat.Prime 4813236448931849 := by
  apply lucas_primality 4813236448931849 (3 : ZMod 4813236448931849)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (577, 1), (2671, 1), (55769849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (577, 1), (2671, 1), (55769849, 1)] : List FactorBlock).map factorBlockValue).prod) = 4813236448931849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_577
      · exact prime_ninetyOneCK_2671
      · exact prime_ninetyOneCK_55769849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4813236448931849) ^ 2406618224465924 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4813236448931849) ^ 687605206990264 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4813236448931849) ^ 8341830934024 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4813236448931849) ^ 1802035360888 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4813236448931849) ^ 86305352 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_5791675924460263 : Nat.Prime 5791675924460263 := by
  apply lucas_primality 5791675924460263 (5 : ZMod 5791675924460263)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5882257, 1), (164100161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5882257, 1), (164100161, 1)] : List FactorBlock).map factorBlockValue).prod) = 5791675924460263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5882257
      · exact prime_ninetyOneCK_164100161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5791675924460263) ^ 2895837962230131 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 5791675924460263) ^ 1930558641486754 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 5791675924460263) ^ 984600966 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 5791675924460263) ^ 35293542 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_6210967925708461 : Nat.Prime 6210967925708461 := by
  apply lucas_primality 6210967925708461 (2 : ZMod 6210967925708461)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (193, 1), (178784338679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (193, 1), (178784338679, 1)] : List FactorBlock).map factorBlockValue).prod) = 6210967925708461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_193
      · exact prime_ninetyOneCK_178784338679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6210967925708461) ^ 3105483962854230 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6210967925708461) ^ 2070322641902820 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6210967925708461) ^ 1242193585141692 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6210967925708461) ^ 32181180962220 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6210967925708461) ^ 34740 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_6334604313196909 : Nat.Prime 6334604313196909 := by
  apply lucas_primality 6334604313196909 (10 : ZMod 6334604313196909)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (101, 1), (223, 1), (1567, 1), (2136707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (101, 1), (223, 1), (1567, 1), (2136707, 1)] : List FactorBlock).map factorBlockValue).prod) = 6334604313196909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_101
      · exact prime_ninetyOneCK_223
      · exact prime_ninetyOneCK_1567
      · exact prime_ninetyOneCK_2136707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6334604313196909) ^ 3167302156598454 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 6334604313196909) ^ 2111534771065636 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 6334604313196909) ^ 904943473313844 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 6334604313196909) ^ 62718854586108 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 6334604313196909) ^ 28406297368596 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 6334604313196909) ^ 4042504347924 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 6334604313196909) ^ 2964657444 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_6516414507954599 : Nat.Prime 6516414507954599 := by
  apply lucas_primality 6516414507954599 (17 : ZMod 6516414507954599)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (61, 1), (79, 1), (4027, 1), (993467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (61, 1), (79, 1), (4027, 1), (993467, 1)] : List FactorBlock).map factorBlockValue).prod) = 6516414507954599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_61
      · exact prime_ninetyOneCK_79
      · exact prime_ninetyOneCK_4027
      · exact prime_ninetyOneCK_993467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 6516414507954599) ^ 3258207253977299 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 6516414507954599) ^ 501262654458046 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 6516414507954599) ^ 106826467343518 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 6516414507954599) ^ 82486259594362 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 6516414507954599) ^ 1618180905874 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 6516414507954599) ^ 6559266194 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_9100155523698223 : Nat.Prime 9100155523698223 := by
  apply lucas_primality 9100155523698223 (21 : ZMod 9100155523698223)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36493, 1), (41561192209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36493, 1), (41561192209, 1)] : List FactorBlock).map factorBlockValue).prod) = 9100155523698223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_36493
      · exact prime_ninetyOneCK_41561192209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 9100155523698223) ^ 4550077761849111 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 9100155523698223) ^ 3033385174566074 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 9100155523698223) ^ 249367153254 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (21 : ZMod 9100155523698223) ^ 218958 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_9626472897863699 : Nat.Prime 9626472897863699 := by
  apply lucas_primality 9626472897863699 (2 : ZMod 9626472897863699)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4813236448931849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4813236448931849, 1)] : List FactorBlock).map factorBlockValue).prod) = 9626472897863699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_4813236448931849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 9626472897863699) ^ 4813236448931849 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 9626472897863699) ^ 2 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_10914413112776441 : Nat.Prime 10914413112776441 := by
  apply lucas_primality 10914413112776441 (3 : ZMod 10914413112776441)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (241, 1), (463, 1), (877, 1), (96149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (241, 1), (463, 1), (877, 1), (96149, 1)] : List FactorBlock).map factorBlockValue).prod) = 10914413112776441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_241
      · exact prime_ninetyOneCK_463
      · exact prime_ninetyOneCK_877
      · exact prime_ninetyOneCK_96149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10914413112776441) ^ 5457206556388220 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 10914413112776441) ^ 2182882622555288 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 10914413112776441) ^ 376359072854360 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 10914413112776441) ^ 45288021214840 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 10914413112776441) ^ 23573246463880 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 10914413112776441) ^ 12445168885720 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 10914413112776441) ^ 113515617560 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_11817666375632699 : Nat.Prime 11817666375632699 := by
  apply lucas_primality 11817666375632699 (2 : ZMod 11817666375632699)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (844119026830907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (844119026830907, 1)] : List FactorBlock).map factorBlockValue).prod) = 11817666375632699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_844119026830907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11817666375632699) ^ 5908833187816349 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11817666375632699) ^ 1688238053661814 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11817666375632699) ^ 14 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_12765918439437391 : Nat.Prime 12765918439437391 := by
  apply lucas_primality 12765918439437391 (6 : ZMod 12765918439437391)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (71, 1), (1997796312901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (71, 1), (1997796312901, 1)] : List FactorBlock).map factorBlockValue).prod) = 12765918439437391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_71
      · exact prime_ninetyOneCK_1997796312901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12765918439437391) ^ 6382959219718695 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12765918439437391) ^ 4255306146479130 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12765918439437391) ^ 2553183687887478 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12765918439437391) ^ 179801668161090 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12765918439437391) ^ 6390 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_21537588965206187 : Nat.Prime 21537588965206187 := by
  apply lucas_primality 21537588965206187 (2 : ZMod 21537588965206187)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (431, 1), (599, 1), (24809, 1), (57977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (431, 1), (599, 1), (24809, 1), (57977, 1)] : List FactorBlock).map factorBlockValue).prod) = 21537588965206187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_431
      · exact prime_ninetyOneCK_599
      · exact prime_ninetyOneCK_24809
      · exact prime_ninetyOneCK_57977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21537588965206187) ^ 10768794482603093 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21537588965206187) ^ 742675481558834 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21537588965206187) ^ 49971204095606 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21537588965206187) ^ 35955908122214 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21537588965206187) ^ 868136118554 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21537588965206187) ^ 371485053818 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_29077914370827683 : Nat.Prime 29077914370827683 := by
  apply lucas_primality 29077914370827683 (2 : ZMod 29077914370827683)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (133384928306549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (133384928306549, 1)] : List FactorBlock).map factorBlockValue).prod) = 29077914370827683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_109
      · exact prime_ninetyOneCK_133384928306549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29077914370827683) ^ 14538957185413841 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29077914370827683) ^ 266769856613098 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29077914370827683) ^ 218 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_29285004561828641 : Nat.Prime 29285004561828641 := by
  apply lucas_primality 29285004561828641 (3 : ZMod 29285004561828641)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (41, 1), (4464177524669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (41, 1), (4464177524669, 1)] : List FactorBlock).map factorBlockValue).prod) = 29285004561828641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_41
      · exact prime_ninetyOneCK_4464177524669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 29285004561828641) ^ 14642502280914320 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 29285004561828641) ^ 5857000912365728 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 29285004561828641) ^ 714268403947040 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 29285004561828641) ^ 6560 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_30622129403623603 : Nat.Prime 30622129403623603 := by
  apply lucas_primality 30622129403623603 (2 : ZMod 30622129403623603)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (31, 1), (2897, 1), (4371501137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (31, 1), (2897, 1), (4371501137, 1)] : List FactorBlock).map factorBlockValue).prod) = 30622129403623603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_31
      · exact prime_ninetyOneCK_2897
      · exact prime_ninetyOneCK_4371501137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30622129403623603) ^ 15311064701811801 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622129403623603) ^ 10207376467874534 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622129403623603) ^ 2355548415663354 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622129403623603) ^ 987810625923342 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622129403623603) ^ 10570289749266 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30622129403623603) ^ 7004946 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_34684276123898839 : Nat.Prime 34684276123898839 := by
  apply lucas_primality 34684276123898839 (3 : ZMod 34684276123898839)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (149, 1), (562271441233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (149, 1), (562271441233, 1)] : List FactorBlock).map factorBlockValue).prod) = 34684276123898839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_149
      · exact prime_ninetyOneCK_562271441233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34684276123898839) ^ 17342138061949419 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34684276123898839) ^ 11561425374632946 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34684276123898839) ^ 1508012005386906 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34684276123898839) ^ 232780376670462 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 34684276123898839) ^ 61686 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_41910600189347557 : Nat.Prime 41910600189347557 := by
  apply lucas_primality 41910600189347557 (2 : ZMod 41910600189347557)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (487, 1), (7171560607349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (487, 1), (7171560607349, 1)] : List FactorBlock).map factorBlockValue).prod) = 41910600189347557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_487
      · exact prime_ninetyOneCK_7171560607349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41910600189347557) ^ 20955300094673778 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 41910600189347557) ^ 13970200063115852 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 41910600189347557) ^ 86058727288188 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 41910600189347557) ^ 5844 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_43156100318554193 : Nat.Prime 43156100318554193 := by
  apply lucas_primality 43156100318554193 (3 : ZMod 43156100318554193)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1780439, 1), (1514938883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1780439, 1), (1514938883, 1)] : List FactorBlock).map factorBlockValue).prod) = 43156100318554193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1780439
      · exact prime_ninetyOneCK_1514938883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43156100318554193) ^ 21578050159277096 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43156100318554193) ^ 24239022128 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 43156100318554193) ^ 28487024 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_50063375224060279 : Nat.Prime 50063375224060279 := by
  apply lucas_primality 50063375224060279 (3 : ZMod 50063375224060279)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1783, 1), (3499, 1), (1337437789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1783, 1), (3499, 1), (1337437789, 1)] : List FactorBlock).map factorBlockValue).prod) = 50063375224060279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_1783
      · exact prime_ninetyOneCK_3499
      · exact prime_ninetyOneCK_1337437789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50063375224060279) ^ 25031687612030139 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 50063375224060279) ^ 16687791741353426 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 50063375224060279) ^ 28078168942266 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 50063375224060279) ^ 14307909466722 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 50063375224060279) ^ 37432302 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_130172572147740893 : Nat.Prime 130172572147740893 := by
  apply lucas_primality 130172572147740893 (2 : ZMod 130172572147740893)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (4363199, 1), (96864301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (4363199, 1), (96864301, 1)] : List FactorBlock).map factorBlockValue).prod) = 130172572147740893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_4363199
      · exact prime_ninetyOneCK_96864301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 130172572147740893) ^ 65086286073870446 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130172572147740893) ^ 18596081735391556 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130172572147740893) ^ 11833870195249172 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130172572147740893) ^ 29834204708 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 130172572147740893) ^ 1343865292 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_150536998912485461 : Nat.Prime 150536998912485461 := by
  apply lucas_primality 150536998912485461 (3 : ZMod 150536998912485461)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (17, 1), (12809, 1), (48593, 1), (64667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (17, 1), (12809, 1), (48593, 1), (64667, 1)] : List FactorBlock).map factorBlockValue).prod) = 150536998912485461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_12809
      · exact prime_ninetyOneCK_48593
      · exact prime_ninetyOneCK_64667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 150536998912485461) ^ 75268499456242730 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 150536998912485461) ^ 30107399782497092 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 150536998912485461) ^ 13685181719316860 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 150536998912485461) ^ 8855117583087380 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 150536998912485461) ^ 11752439605940 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 150536998912485461) ^ 3097915315220 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 150536998912485461) ^ 2327879736380 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_234272759512696337 : Nat.Prime 234272759512696337 := by
  apply lucas_primality 234272759512696337 (3 : ZMod 234272759512696337)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (504898188604949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (504898188604949, 1)] : List FactorBlock).map factorBlockValue).prod) = 234272759512696337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_504898188604949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 234272759512696337) ^ 117136379756348168 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 234272759512696337) ^ 8078371017679184 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 234272759512696337) ^ 464 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_249042136914971731 : Nat.Prime 249042136914971731 := by
  apply lucas_primality 249042136914971731 (10 : ZMod 249042136914971731)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 2), (19, 2), (159361, 1), (397517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 2), (19, 2), (159361, 1), (397517, 1)] : List FactorBlock).map factorBlockValue).prod) = 249042136914971731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_159361
      · exact prime_ninetyOneCK_397517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 249042136914971731) ^ 124521068457485865 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 249042136914971731) ^ 83014045638323910 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 249042136914971731) ^ 49808427382994346 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 249042136914971731) ^ 22640194264997430 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 249042136914971731) ^ 13107480890261670 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 249042136914971731) ^ 1562754606930 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 249042136914971731) ^ 626494305690 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_328470825021742859 : Nat.Prime 328470825021742859 := by
  apply lucas_primality 328470825021742859 (2 : ZMod 328470825021742859)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (23, 1), (6036069407581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (23, 1), (6036069407581, 1)] : List FactorBlock).map factorBlockValue).prod) = 328470825021742859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_6036069407581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 328470825021742859) ^ 164235412510871429 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 328470825021742859) ^ 46924403574534694 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 328470825021742859) ^ 25266986540134066 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 328470825021742859) ^ 14281340218336646 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 328470825021742859) ^ 54418 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_412673672030129617 : Nat.Prime 412673672030129617 := by
  apply lucas_primality 412673672030129617 (5 : ZMod 412673672030129617)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (59, 1), (46523, 1), (3132173431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (59, 1), (46523, 1), (3132173431, 1)] : List FactorBlock).map factorBlockValue).prod) = 412673672030129617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_59
      · exact prime_ninetyOneCK_46523
      · exact prime_ninetyOneCK_3132173431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 412673672030129617) ^ 206336836015064808 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 412673672030129617) ^ 137557890676709872 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 412673672030129617) ^ 6994469017459824 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 412673672030129617) ^ 8870315156592 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 412673672030129617) ^ 131753136 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_481014619213032493 : Nat.Prime 481014619213032493 := by
  apply lucas_primality 481014619213032493 (11 : ZMod 481014619213032493)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (29, 1), (71, 1), (191, 1), (633084149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (29, 1), (71, 1), (191, 1), (633084149, 1)] : List FactorBlock).map factorBlockValue).prod) = 481014619213032493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_29
      · exact prime_ninetyOneCK_71
      · exact prime_ninetyOneCK_191
      · exact prime_ninetyOneCK_633084149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 481014619213032493) ^ 240507309606516246 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 481014619213032493) ^ 160338206404344164 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 481014619213032493) ^ 68716374173290356 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 481014619213032493) ^ 20913679096218804 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 481014619213032493) ^ 16586711007345948 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 481014619213032493) ^ 6774853791732852 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 481014619213032493) ^ 2518401147712212 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 481014619213032493) ^ 759795708 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_526141308360718781 : Nat.Prime 526141308360718781 := by
  apply lucas_primality 526141308360718781 (2 : ZMod 526141308360718781)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (8167, 1), (179591, 1), (17935987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (8167, 1), (179591, 1), (17935987, 1)] : List FactorBlock).map factorBlockValue).prod) = 526141308360718781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_8167
      · exact prime_ninetyOneCK_179591
      · exact prime_ninetyOneCK_17935987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 526141308360718781) ^ 263070654180359390 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 526141308360718781) ^ 105228261672143756 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 526141308360718781) ^ 64422836826340 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 526141308360718781) ^ 2929664116580 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 526141308360718781) ^ 29334393940 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_720676796052012263 : Nat.Prime 720676796052012263 := by
  apply lucas_primality 720676796052012263 (5 : ZMod 720676796052012263)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (80071, 1), (98047, 1), (580997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (80071, 1), (98047, 1), (580997, 1)] : List FactorBlock).map factorBlockValue).prod) = 720676796052012263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_79
      · exact prime_ninetyOneCK_80071
      · exact prime_ninetyOneCK_98047
      · exact prime_ninetyOneCK_580997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 720676796052012263) ^ 360338398026006131 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 720676796052012263) ^ 9122491089265978 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 720676796052012263) ^ 9000472031722 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 720676796052012263) ^ 7350319704346 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 720676796052012263) ^ 1240413971246 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1023482288918665943 : Nat.Prime 1023482288918665943 := by
  apply lucas_primality 1023482288918665943 (5 : ZMod 1023482288918665943)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (48049, 1), (10650401557979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (48049, 1), (10650401557979, 1)] : List FactorBlock).map factorBlockValue).prod) = 1023482288918665943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_48049
      · exact prime_ninetyOneCK_10650401557979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1023482288918665943) ^ 511741144459332971 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1023482288918665943) ^ 21300803115958 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1023482288918665943) ^ 96098 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1408617952566685739 : Nat.Prime 1408617952566685739 := by
  apply lucas_primality 1408617952566685739 (2 : ZMod 1408617952566685739)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (30622129403623603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (30622129403623603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408617952566685739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_30622129403623603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1408617952566685739) ^ 704308976283342869 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408617952566685739) ^ 61244258807247206 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408617952566685739) ^ 46 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1494252821489830387 : Nat.Prime 1494252821489830387 := by
  apply lucas_primality 1494252821489830387 (2 : ZMod 1494252821489830387)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (249042136914971731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (249042136914971731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1494252821489830387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_249042136914971731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1494252821489830387) ^ 747126410744915193 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1494252821489830387) ^ 498084273829943462 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1494252821489830387) ^ 6 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_7366315822800385643 : Nat.Prime 7366315822800385643 := by
  apply lucas_primality 7366315822800385643 (2 : ZMod 7366315822800385643)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (11279, 1), (2349280869841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (11279, 1), (2349280869841, 1)] : List FactorBlock).map factorBlockValue).prod) = 7366315822800385643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_139
      · exact prime_ninetyOneCK_11279
      · exact prime_ninetyOneCK_2349280869841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7366315822800385643) ^ 3683157911400192821 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7366315822800385643) ^ 52995077861873278 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7366315822800385643) ^ 653100081815798 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7366315822800385643) ^ 3135562 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_7409379533160921293 : Nat.Prime 7409379533160921293 := by
  apply lucas_primality 7409379533160921293 (2 : ZMod 7409379533160921293)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (50063375224060279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (50063375224060279, 1)] : List FactorBlock).map factorBlockValue).prod) = 7409379533160921293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_37
      · exact prime_ninetyOneCK_50063375224060279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7409379533160921293) ^ 3704689766580460646 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7409379533160921293) ^ 200253500896241116 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7409379533160921293) ^ 148 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_8228480856114563893 : Nat.Prime 8228480856114563893 := by
  apply lucas_primality 8228480856114563893 (2 : ZMod 8228480856114563893)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 2), (790895891591173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 2), (790895891591173, 1)] : List FactorBlock).map factorBlockValue).prod) = 8228480856114563893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_790895891591173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8228480856114563893) ^ 4114240428057281946 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8228480856114563893) ^ 2742826952038187964 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8228480856114563893) ^ 484028285653797876 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8228480856114563893) ^ 10404 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_22885746341387715337 : Nat.Prime 22885746341387715337 := by
  apply lucas_primality 22885746341387715337 (5 : ZMod 22885746341387715337)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (239, 1), (16111, 1), (13034063689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (239, 1), (16111, 1), (13034063689, 1)] : List FactorBlock).map factorBlockValue).prod) = 22885746341387715337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_239
      · exact prime_ninetyOneCK_16111
      · exact prime_ninetyOneCK_13034063689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22885746341387715337) ^ 11442873170693857668 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 22885746341387715337) ^ 7628582113795905112 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 22885746341387715337) ^ 1204512965336195544 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 22885746341387715337) ^ 95756260842626424 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 22885746341387715337) ^ 1420504397081976 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 22885746341387715337) ^ 1755841224 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_22909912043573142059 : Nat.Prime 22909912043573142059 := by
  apply lucas_primality 22909912043573142059 (2 : ZMod 22909912043573142059)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (6197, 1), (68351, 1), (1175815609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (6197, 1), (68351, 1), (1175815609, 1)] : List FactorBlock).map factorBlockValue).prod) = 22909912043573142059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_6197
      · exact prime_ninetyOneCK_68351
      · exact prime_ninetyOneCK_1175815609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22909912043573142059) ^ 11454956021786571029 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22909912043573142059) ^ 996083132329267046 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22909912043573142059) ^ 3696935943774914 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22909912043573142059) ^ 335180349132758 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 22909912043573142059) ^ 19484272762 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_25668707697207885617 : Nat.Prime 25668707697207885617 := by
  apply lucas_primality 25668707697207885617 (3 : ZMod 25668707697207885617)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (277, 1), (5791675924460263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (277, 1), (5791675924460263, 1)] : List FactorBlock).map factorBlockValue).prod) = 25668707697207885617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_277
      · exact prime_ninetyOneCK_5791675924460263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25668707697207885617) ^ 12834353848603942808 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 25668707697207885617) ^ 92666814791364208 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 25668707697207885617) ^ 4432 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_61518368590179044281 : Nat.Prime 61518368590179044281 := by
  apply lucas_primality 61518368590179044281 (14 : ZMod 61518368590179044281)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 2), (19, 1), (5101, 1), (47093, 1), (928267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 2), (19, 1), (5101, 1), (47093, 1), (928267, 1)] : List FactorBlock).map factorBlockValue).prod) = 61518368590179044281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_5101
      · exact prime_ninetyOneCK_47093
      · exact prime_ninetyOneCK_928267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 61518368590179044281) ^ 30759184295089522140 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 61518368590179044281) ^ 20506122863393014760 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 61518368590179044281) ^ 12303673718035808856 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 61518368590179044281) ^ 5592578962743549480 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 61518368590179044281) ^ 3237808873167318120 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 61518368590179044281) ^ 12060060496016280 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 61518368590179044281) ^ 1306316620095960 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (14 : ZMod 61518368590179044281) ^ 66272277900840 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_103734757241082384569 : Nat.Prime 103734757241082384569 := by
  apply lucas_primality 103734757241082384569 (3 : ZMod 103734757241082384569)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (179, 1), (373, 1), (194210383200313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (179, 1), (373, 1), (194210383200313, 1)] : List FactorBlock).map factorBlockValue).prod) = 103734757241082384569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_179
      · exact prime_ninetyOneCK_373
      · exact prime_ninetyOneCK_194210383200313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 103734757241082384569) ^ 51867378620541192284 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 103734757241082384569) ^ 579523783469733992 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 103734757241082384569) ^ 278109268742848216 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 103734757241082384569) ^ 534136 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_135302640529346495323 : Nat.Prime 135302640529346495323 := by
  apply lucas_primality 135302640529346495323 (2 : ZMod 135302640529346495323)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (49789, 1), (34840009591591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (49789, 1), (34840009591591, 1)] : List FactorBlock).map factorBlockValue).prod) = 135302640529346495323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_49789
      · exact prime_ninetyOneCK_34840009591591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135302640529346495323) ^ 67651320264673247661 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135302640529346495323) ^ 45100880176448831774 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135302640529346495323) ^ 10407895425334345794 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135302640529346495323) ^ 2717520748144098 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 135302640529346495323) ^ 3883542 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_137985776192462209723 : Nat.Prime 137985776192462209723 := by
  apply lucas_primality 137985776192462209723 (2 : ZMod 137985776192462209723)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (9941, 1), (68227, 1), (1255836083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (9941, 1), (68227, 1), (1255836083, 1)] : List FactorBlock).map factorBlockValue).prod) = 137985776192462209723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_9941
      · exact prime_ninetyOneCK_68227
      · exact prime_ninetyOneCK_1255836083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137985776192462209723) ^ 68992888096231104861 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137985776192462209723) ^ 45995258730820736574 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137985776192462209723) ^ 13880472406444242 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137985776192462209723) ^ 2022451173178686 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 137985776192462209723) ^ 109875626334 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_207469514482164769139 : Nat.Prime 207469514482164769139 := by
  apply lucas_primality 207469514482164769139 (2 : ZMod 207469514482164769139)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103734757241082384569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103734757241082384569, 1)] : List FactorBlock).map factorBlockValue).prod) = 207469514482164769139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_103734757241082384569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 207469514482164769139) ^ 103734757241082384569 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 207469514482164769139) ^ 2 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_542445613126892949791 : Nat.Prime 542445613126892949791 := by
  apply lucas_primality 542445613126892949791 (7 : ZMod 542445613126892949791)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (1023482288918665943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (1023482288918665943, 1)] : List FactorBlock).map factorBlockValue).prod) = 542445613126892949791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_53
      · exact prime_ninetyOneCK_1023482288918665943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 542445613126892949791) ^ 271222806563446474895 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 542445613126892949791) ^ 108489122625378589958 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 542445613126892949791) ^ 10234822889186659430 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 542445613126892949791) ^ 530 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_979824164474184004739 : Nat.Prime 979824164474184004739 := by
  apply lucas_primality 979824164474184004739 (2 : ZMod 979824164474184004739)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (5323, 1), (355354582203617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (5323, 1), (355354582203617, 1)] : List FactorBlock).map factorBlockValue).prod) = 979824164474184004739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_37
      · exact prime_ninetyOneCK_5323
      · exact prime_ninetyOneCK_355354582203617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 979824164474184004739) ^ 489912082237092002369 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 979824164474184004739) ^ 139974880639169143534 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 979824164474184004739) ^ 26481734174977946074 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 979824164474184004739) ^ 184073673581473606 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 979824164474184004739) ^ 2757314 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1553779172288138439029 : Nat.Prime 1553779172288138439029 := by
  apply lucas_primality 1553779172288138439029 (2 : ZMod 1553779172288138439029)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11, 1), (720676796052012263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11, 1), (720676796052012263, 1)] : List FactorBlock).map factorBlockValue).prod) = 1553779172288138439029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_720676796052012263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1553779172288138439029) ^ 776889586144069219514 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1553779172288138439029) ^ 221968453184019777004 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1553779172288138439029) ^ 141252652026194403548 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1553779172288138439029) ^ 2156 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1605673778290762660979 : Nat.Prime 1605673778290762660979 := by
  apply lucas_primality 1605673778290762660979 (2 : ZMod 1605673778290762660979)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (43, 1), (107, 1), (344819, 1), (16323835301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (43, 1), (107, 1), (344819, 1), (16323835301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1605673778290762660979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_31
      · exact prime_ninetyOneCK_43
      · exact prime_ninetyOneCK_107
      · exact prime_ninetyOneCK_344819
      · exact prime_ninetyOneCK_16323835301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1605673778290762660979) ^ 802836889145381330489 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1605673778290762660979) ^ 51795928331960085838 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1605673778290762660979) ^ 37341250657924713046 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1605673778290762660979) ^ 15006296993371613654 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1605673778290762660979) ^ 4656569905633862 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1605673778290762660979) ^ 98363757578 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1676620476794038255157 : Nat.Prime 1676620476794038255157 := by
  apply lucas_primality 1676620476794038255157 (2 : ZMod 1676620476794038255157)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3940483559, 1), (106371492971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3940483559, 1), (106371492971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1676620476794038255157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3940483559
      · exact prime_ninetyOneCK_106371492971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1676620476794038255157) ^ 838310238397019127578 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1676620476794038255157) ^ 425485971884 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1676620476794038255157) ^ 15761934236 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2238869236353733129469 : Nat.Prime 2238869236353733129469 := by
  apply lucas_primality 2238869236353733129469 (2 : ZMod 2238869236353733129469)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 4), (83898049, 1), (2778591583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 4), (83898049, 1), (2778591583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2238869236353733129469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_83898049
      · exact prime_ninetyOneCK_2778591583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2238869236353733129469) ^ 1119434618176866564734 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238869236353733129469) ^ 319838462336247589924 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238869236353733129469) ^ 26685593563132 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2238869236353733129469) ^ 805756862596 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_2950080212193655409731 : Nat.Prime 2950080212193655409731 := by
  apply lucas_primality 2950080212193655409731 (3 : ZMod 2950080212193655409731)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (166871, 1), (196431189507907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (166871, 1), (196431189507907, 1)] : List FactorBlock).map factorBlockValue).prod) = 2950080212193655409731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_166871
      · exact prime_ninetyOneCK_196431189507907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2950080212193655409731) ^ 1475040106096827704865 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2950080212193655409731) ^ 983360070731218469910 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2950080212193655409731) ^ 590016042438731081946 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2950080212193655409731) ^ 17678807055711630 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2950080212193655409731) ^ 15018390 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3107558344576276878059 : Nat.Prime 3107558344576276878059 := by
  apply lucas_primality 3107558344576276878059 (2 : ZMod 3107558344576276878059)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1553779172288138439029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1553779172288138439029, 1)] : List FactorBlock).map factorBlockValue).prod) = 3107558344576276878059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1553779172288138439029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3107558344576276878059) ^ 1553779172288138439029 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3107558344576276878059) ^ 2 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_7380914176424196427013 : Nat.Prime 7380914176424196427013 := by
  apply lucas_primality 7380914176424196427013 (2 : ZMod 7380914176424196427013)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (53, 1), (222778403, 1), (22325601481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (53, 1), (222778403, 1), (22325601481, 1)] : List FactorBlock).map factorBlockValue).prod) = 7380914176424196427013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_53
      · exact prime_ninetyOneCK_222778403
      · exact prime_ninetyOneCK_22325601481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7380914176424196427013) ^ 3690457088212098213506 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7380914176424196427013) ^ 1054416310917742346716 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7380914176424196427013) ^ 139262531630645215604 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7380914176424196427013) ^ 33131192597804 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7380914176424196427013) ^ 330603150052 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_7830607783084665682393 : Nat.Prime 7830607783084665682393 := by
  apply lucas_primality 7830607783084665682393 (5 : ZMod 7830607783084665682393)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (104590259, 1), (346617497243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (104590259, 1), (346617497243, 1)] : List FactorBlock).map factorBlockValue).prod) = 7830607783084665682393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_104590259
      · exact prime_ninetyOneCK_346617497243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7830607783084665682393) ^ 3915303891542332841196 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 7830607783084665682393) ^ 2610202594361555227464 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 7830607783084665682393) ^ 74869379404488 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 7830607783084665682393) ^ 22591495944 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_8368326610855946153963 : Nat.Prime 8368326610855946153963 := by
  apply lucas_primality 8368326610855946153963 (2 : ZMod 8368326610855946153963)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (283, 1), (159569, 1), (850055280667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (283, 1), (159569, 1), (850055280667, 1)] : List FactorBlock).map factorBlockValue).prod) = 8368326610855946153963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_109
      · exact prime_ninetyOneCK_283
      · exact prime_ninetyOneCK_159569
      · exact prime_ninetyOneCK_850055280667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8368326610855946153963) ^ 4184163305427973076981 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8368326610855946153963) ^ 76773638631705928018 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8368326610855946153963) ^ 29570058695604050014 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8368326610855946153963) ^ 52443310485469898 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8368326610855946153963) ^ 9844449886 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_57378618328809038574191 : Nat.Prime 57378618328809038574191 := by
  apply lucas_primality 57378618328809038574191 (7 : ZMod 57378618328809038574191)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4663, 1), (14411, 1), (85386763552583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4663, 1), (14411, 1), (85386763552583, 1)] : List FactorBlock).map factorBlockValue).prod) = 57378618328809038574191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_4663
      · exact prime_ninetyOneCK_14411
      · exact prime_ninetyOneCK_85386763552583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 57378618328809038574191) ^ 28689309164404519287095 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 57378618328809038574191) ^ 11475723665761807714838 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 57378618328809038574191) ^ 12305086495562736130 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 57378618328809038574191) ^ 3981584784456945290 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (7 : ZMod 57378618328809038574191) ^ 671984930 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_71975192456732002565971 : Nat.Prime 71975192456732002565971 := by
  apply lucas_primality 71975192456732002565971 (2 : ZMod 71975192456732002565971)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (74280181, 1), (319791748079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (74280181, 1), (319791748079, 1)] : List FactorBlock).map factorBlockValue).prod) = 71975192456732002565971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_101
      · exact prime_ninetyOneCK_74280181
      · exact prime_ninetyOneCK_319791748079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71975192456732002565971) ^ 35987596228366001282985 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 71975192456732002565971) ^ 23991730818910667521990 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 71975192456732002565971) ^ 14395038491346400513194 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 71975192456732002565971) ^ 712625667888435668970 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 71975192456732002565971) ^ 968968996679370 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 71975192456732002565971) ^ 225068948430 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_110738000691024074940413 : Nat.Prime 110738000691024074940413 := by
  apply lucas_primality 110738000691024074940413 (2 : ZMod 110738000691024074940413)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1760659, 1), (3916169, 1), (4015133693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1760659, 1), (3916169, 1), (4015133693, 1)] : List FactorBlock).map factorBlockValue).prod) = 110738000691024074940413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1760659
      · exact prime_ninetyOneCK_3916169
      · exact prime_ninetyOneCK_4015133693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110738000691024074940413) ^ 55369000345512037470206 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 110738000691024074940413) ^ 62895768397528468 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 110738000691024074940413) ^ 28277125091134748 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 110738000691024074940413) ^ 27580152781484 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_117156572551983246155483 : Nat.Prime 117156572551983246155483 := by
  apply lucas_primality 117156572551983246155483 (2 : ZMod 117156572551983246155483)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (8368326610855946153963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (8368326610855946153963, 1)] : List FactorBlock).map factorBlockValue).prod) = 117156572551983246155483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_8368326610855946153963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 117156572551983246155483) ^ 58578286275991623077741 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 117156572551983246155483) ^ 16736653221711892307926 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 117156572551983246155483) ^ 14 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_133983768528925799825069 : Nat.Prime 133983768528925799825069 := by
  apply lucas_primality 133983768528925799825069 (2 : ZMod 133983768528925799825069)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (14737, 1), (11781949, 1), (2119944949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (14737, 1), (11781949, 1), (2119944949, 1)] : List FactorBlock).map factorBlockValue).prod) = 133983768528925799825069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_13
      · exact prime_ninetyOneCK_14737
      · exact prime_ninetyOneCK_11781949
      · exact prime_ninetyOneCK_2119944949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 133983768528925799825069) ^ 66991884264462899912534 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133983768528925799825069) ^ 19140538361275114260724 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133983768528925799825069) ^ 10306443732994292294236 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133983768528925799825069) ^ 9091658310980918764 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133983768528925799825069) ^ 11371952851682332 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 133983768528925799825069) ^ 63201531998332 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_256539580216648199686519 : Nat.Prime 256539580216648199686519 := by
  apply lucas_primality 256539580216648199686519 (3 : ZMod 256539580216648199686519)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (379, 1), (1459, 1), (3361869038391551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (379, 1), (1459, 1), (3361869038391551, 1)] : List FactorBlock).map factorBlockValue).prod) = 256539580216648199686519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_379
      · exact prime_ninetyOneCK_1459
      · exact prime_ninetyOneCK_3361869038391551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 256539580216648199686519) ^ 128269790108324099843259 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 256539580216648199686519) ^ 85513193405549399895506 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 256539580216648199686519) ^ 11153894792028182595066 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 256539580216648199686519) ^ 676885435927831661442 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 256539580216648199686519) ^ 175832474445954900402 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 256539580216648199686519) ^ 76308618 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_336026530906377942929219 : Nat.Prime 336026530906377942929219 := by
  apply lucas_primality 336026530906377942929219 (2 : ZMod 336026530906377942929219)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1723, 1), (307103, 1), (12933989, 1), (24549449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1723, 1), (307103, 1), (12933989, 1), (24549449, 1)] : List FactorBlock).map factorBlockValue).prod) = 336026530906377942929219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1723
      · exact prime_ninetyOneCK_307103
      · exact prime_ninetyOneCK_12933989
      · exact prime_ninetyOneCK_24549449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 336026530906377942929219) ^ 168013265453188971464609 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 336026530906377942929219) ^ 195024103834229798566 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 336026530906377942929219) ^ 1094181857247822206 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 336026530906377942929219) ^ 25980115717307162 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 336026530906377942929219) ^ 13687742275045682 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_371710106736400581626107 : Nat.Prime 371710106736400581626107 := by
  apply lucas_primality 371710106736400581626107 (2 : ZMod 371710106736400581626107)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2950080212193655409731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2950080212193655409731, 1)] : List FactorBlock).map factorBlockValue).prod) = 371710106736400581626107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_2950080212193655409731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 371710106736400581626107) ^ 185855053368200290813053 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 371710106736400581626107) ^ 123903368912133527208702 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 371710106736400581626107) ^ 53101443819485797375158 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 371710106736400581626107) ^ 126 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_763971499757549005812419 : Nat.Prime 763971499757549005812419 := by
  apply lucas_primality 763971499757549005812419 (2 : ZMod 763971499757549005812419)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (3094277, 1), (1691083734645829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (3094277, 1), (1691083734645829, 1)] : List FactorBlock).map factorBlockValue).prod) = 763971499757549005812419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_73
      · exact prime_ninetyOneCK_3094277
      · exact prime_ninetyOneCK_1691083734645829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 763971499757549005812419) ^ 381985749878774502906209 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 763971499757549005812419) ^ 10465363010377383641266 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 763971499757549005812419) ^ 246898225258291034 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 763971499757549005812419) ^ 451764442 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1347456120101157741890861 : Nat.Prime 1347456120101157741890861 := by
  apply lucas_primality 1347456120101157741890861 (2 : ZMod 1347456120101157741890861)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (199, 1), (156631, 1), (2161493025619247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (199, 1), (156631, 1), (2161493025619247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1347456120101157741890861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_199
      · exact prime_ninetyOneCK_156631
      · exact prime_ninetyOneCK_2161493025619247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1347456120101157741890861) ^ 673728060050578870945430 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1347456120101157741890861) ^ 269491224020231548378172 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1347456120101157741890861) ^ 6771136281915365537140 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1347456120101157741890861) ^ 8602742241964603060 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1347456120101157741890861) ^ 623391380 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_5821768747476019412528891 : Nat.Prime 5821768747476019412528891 := by
  apply lucas_primality 5821768747476019412528891 (2 : ZMod 5821768747476019412528891)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (91904221, 1), (6334604313196909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (91904221, 1), (6334604313196909, 1)] : List FactorBlock).map factorBlockValue).prod) = 5821768747476019412528891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_91904221
      · exact prime_ninetyOneCK_6334604313196909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5821768747476019412528891) ^ 2910884373738009706264445 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5821768747476019412528891) ^ 1164353749495203882505778 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5821768747476019412528891) ^ 63346043131969090 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5821768747476019412528891) ^ 919042210 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_7541975916814359533370761 : Nat.Prime 7541975916814359533370761 := by
  apply lucas_primality 7541975916814359533370761 (6 : ZMod 7541975916814359533370761)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 2), (19, 1), (397, 1), (1223, 1), (10687, 1), (26497, 1), (1473011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 2), (19, 1), (397, 1), (1223, 1), (10687, 1), (26497, 1), (1473011, 1)] : List FactorBlock).map factorBlockValue).prod) = 7541975916814359533370761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_397
      · exact prime_ninetyOneCK_1223
      · exact prime_ninetyOneCK_10687
      · exact prime_ninetyOneCK_26497
      · exact prime_ninetyOneCK_1473011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7541975916814359533370761) ^ 3770987958407179766685380 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7541975916814359533370761) ^ 1508395183362871906674152 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7541975916814359533370761) ^ 1077425130973479933338680 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7541975916814359533370761) ^ 396946100884966291230040 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7541975916814359533370761) ^ 18997420445376220487080 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7541975916814359533370761) ^ 6166783251687947288120 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7541975916814359533370761) ^ 705714973034000143480 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7541975916814359533370761) ^ 284635087625556083080 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7541975916814359533370761) ^ 5120108347333699160 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_18769414943014103060630479 : Nat.Prime 18769414943014103060630479 := by
  apply lucas_primality 18769414943014103060630479 (3 : ZMod 18769414943014103060630479)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (31, 1), (443167, 1), (937052889331583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (31, 1), (443167, 1), (937052889331583, 1)] : List FactorBlock).map factorBlockValue).prod) = 18769414943014103060630479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_31
      · exact prime_ninetyOneCK_443167
      · exact prime_ninetyOneCK_937052889331583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18769414943014103060630479) ^ 9384707471507051530315239 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 18769414943014103060630479) ^ 6256471647671367686876826 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 18769414943014103060630479) ^ 605464998161745260020338 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 18769414943014103060630479) ^ 42352916492008888434 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 18769414943014103060630479) ^ 20030262066 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_37098719466674771980528933 : Nat.Prime 37098719466674771980528933 := by
  apply lucas_primality 37098719466674771980528933 (2 : ZMod 37098719466674771980528933)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (223, 1), (75797, 1), (9626472897863699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (223, 1), (75797, 1), (9626472897863699, 1)] : List FactorBlock).map factorBlockValue).prod) = 37098719466674771980528933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_19
      · exact prime_ninetyOneCK_223
      · exact prime_ninetyOneCK_75797
      · exact prime_ninetyOneCK_9626472897863699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37098719466674771980528933) ^ 18549359733337385990264466 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37098719466674771980528933) ^ 12366239822224923993509644 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37098719466674771980528933) ^ 1952564182456566946343628 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37098719466674771980528933) ^ 166361970702577452827484 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37098719466674771980528933) ^ 489448388018981911956 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 37098719466674771980528933) ^ 3853822668 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_46553996734468558521650327 : Nat.Prime 46553996734468558521650327 := by
  apply lucas_primality 46553996734468558521650327 (5 : ZMod 46553996734468558521650327)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (242083, 1), (412673672030129617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (242083, 1), (412673672030129617, 1)] : List FactorBlock).map factorBlockValue).prod) = 46553996734468558521650327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_233
      · exact prime_ninetyOneCK_242083
      · exact prime_ninetyOneCK_412673672030129617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 46553996734468558521650327) ^ 23276998367234279260825163 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 46553996734468558521650327) ^ 199802561092139736144422 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 46553996734468558521650327) ^ 192305931166040401522 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 46553996734468558521650327) ^ 112810678 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_48137040918727892055272441 : Nat.Prime 48137040918727892055272441 := by
  apply lucas_primality 48137040918727892055272441 (3 : ZMod 48137040918727892055272441)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (173, 1), (271, 1), (25668707697207885617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (173, 1), (271, 1), (25668707697207885617, 1)] : List FactorBlock).map factorBlockValue).prod) = 48137040918727892055272441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_173
      · exact prime_ninetyOneCK_271
      · exact prime_ninetyOneCK_25668707697207885617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48137040918727892055272441) ^ 24068520459363946027636220 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48137040918727892055272441) ^ 9627408183745578411054488 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48137040918727892055272441) ^ 278248791437733480088280 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48137040918727892055272441) ^ 177627457264678568469640 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 48137040918727892055272441) ^ 1875320 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_83464923547988237970158189 : Nat.Prime 83464923547988237970158189 := by
  apply lucas_primality 83464923547988237970158189 (2 : ZMod 83464923547988237970158189)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (339187, 1), (61518368590179044281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (339187, 1), (61518368590179044281, 1)] : List FactorBlock).map factorBlockValue).prod) = 83464923547988237970158189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_339187
      · exact prime_ninetyOneCK_61518368590179044281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 83464923547988237970158189) ^ 41732461773994118985079094 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83464923547988237970158189) ^ 246073474360716177124 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 83464923547988237970158189) ^ 1356748 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_116687946261775313170861069 : Nat.Prime 116687946261775313170861069 := by
  apply lucas_primality 116687946261775313170861069 (6 : ZMod 116687946261775313170861069)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (117156572551983246155483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (117156572551983246155483, 1)] : List FactorBlock).map factorBlockValue).prod) = 116687946261775313170861069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_83
      · exact prime_ninetyOneCK_117156572551983246155483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 116687946261775313170861069) ^ 58343973130887656585430534 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 116687946261775313170861069) ^ 38895982087258437723620356 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 116687946261775313170861069) ^ 1405878870623798953865796 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (6 : ZMod 116687946261775313170861069) ^ 996 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_420258931458425151341929319 : Nat.Prime 420258931458425151341929319 := by
  apply lucas_primality 420258931458425151341929319 (17 : ZMod 420258931458425151341929319)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (491, 1), (3163, 1), (135302640529346495323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (491, 1), (3163, 1), (135302640529346495323, 1)] : List FactorBlock).map factorBlockValue).prod) = 420258931458425151341929319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_491
      · exact prime_ninetyOneCK_3163
      · exact prime_ninetyOneCK_135302640529346495323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 420258931458425151341929319) ^ 210129465729212575670964659 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 420258931458425151341929319) ^ 855924503988645929413298 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 420258931458425151341929319) ^ 132867192999818258407186 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (17 : ZMod 420258931458425151341929319) ^ 3106066 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_1044527052945212026636251511 : Nat.Prime 1044527052945212026636251511 := by
  apply lucas_primality 1044527052945212026636251511 (3 : ZMod 1044527052945212026636251511)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (93077, 1), (2133973, 1), (58431345368959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (93077, 1), (2133973, 1), (58431345368959, 1)] : List FactorBlock).map factorBlockValue).prod) = 1044527052945212026636251511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_93077
      · exact prime_ninetyOneCK_2133973
      · exact prime_ninetyOneCK_58431345368959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1044527052945212026636251511) ^ 522263526472606013318125755 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044527052945212026636251511) ^ 348175684315070675545417170 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044527052945212026636251511) ^ 208905410589042405327250302 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044527052945212026636251511) ^ 11222182203393018969630 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044527052945212026636251511) ^ 489475289961593715870 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1044527052945212026636251511) ^ 17876142442890 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_3709871946667477198052893297 : Nat.Prime 3709871946667477198052893297 := by
  apply lucas_primality 3709871946667477198052893297 (5 : ZMod 3709871946667477198052893297)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (449, 1), (57378618328809038574191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (449, 1), (57378618328809038574191, 1)] : List FactorBlock).map factorBlockValue).prod) = 3709871946667477198052893297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_449
      · exact prime_ninetyOneCK_57378618328809038574191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3709871946667477198052893297) ^ 1854935973333738599026446648 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3709871946667477198052893297) ^ 1236623982222492399350964432 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3709871946667477198052893297) ^ 8262521039348501554683504 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3709871946667477198052893297) ^ 64656 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_4890285747879856306524268439 : Nat.Prime 4890285747879856306524268439 := by
  apply lucas_primality 4890285747879856306524268439 (11 : ZMod 4890285747879856306524268439)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (229, 1), (18108697, 1), (34684276123898839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (229, 1), (18108697, 1), (34684276123898839, 1)] : List FactorBlock).map factorBlockValue).prod) = 4890285747879856306524268439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_17
      · exact prime_ninetyOneCK_229
      · exact prime_ninetyOneCK_18108697
      · exact prime_ninetyOneCK_34684276123898839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4890285747879856306524268439) ^ 2445142873939928153262134219 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4890285747879856306524268439) ^ 287663867522344488619074614 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4890285747879856306524268439) ^ 21354959597728630159494622 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4890285747879856306524268439) ^ 270051773900676360454 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (11 : ZMod 4890285747879856306524268439) ^ 140994314842 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_5379314322667841937176695283 : Nat.Prime 5379314322667841937176695283 := by
  apply lucas_primality 5379314322667841937176695283 (2 : ZMod 5379314322667841937176695283)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (952285781, 1), (11817666375632699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (952285781, 1), (11817666375632699, 1)] : List FactorBlock).map factorBlockValue).prod) = 5379314322667841937176695283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_239
      · exact prime_ninetyOneCK_952285781
      · exact prime_ninetyOneCK_11817666375632699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5379314322667841937176695283) ^ 2689657161333920968588347641 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5379314322667841937176695283) ^ 22507591308233648272705838 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5379314322667841937176695283) ^ 5648844527552430122 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5379314322667841937176695283) ^ 455192603318 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_8965523871113069895294492137 : Nat.Prime 8965523871113069895294492137 := by
  apply lucas_primality 8965523871113069895294492137 (3 : ZMod 8965523871113069895294492137)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (37, 1), (43, 1), (349, 1), (1499, 1), (136756897, 1), (428066627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (37, 1), (43, 1), (349, 1), (1499, 1), (136756897, 1), (428066627, 1)] : List FactorBlock).map factorBlockValue).prod) = 8965523871113069895294492137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_23
      · exact prime_ninetyOneCK_37
      · exact prime_ninetyOneCK_43
      · exact prime_ninetyOneCK_349
      · exact prime_ninetyOneCK_1499
      · exact prime_ninetyOneCK_136756897
      · exact prime_ninetyOneCK_428066627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8965523871113069895294492137) ^ 4482761935556534947647246068 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8965523871113069895294492137) ^ 389805385700568256317151832 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8965523871113069895294492137) ^ 242311455976028916089040328 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8965523871113069895294492137) ^ 208500555142164416169639352 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8965523871113069895294492137) ^ 25689180146455787665600264 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8965523871113069895294492137) ^ 5981003249575096661303864 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8965523871113069895294492137) ^ 65558111274732051688 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 8965523871113069895294492137) ^ 20944225280876824568 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_10758628645335683874353390569 : Nat.Prime 10758628645335683874353390569 := by
  apply lucas_primality 10758628645335683874353390569 (23 : ZMod 10758628645335683874353390569)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (5821768747476019412528891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (5821768747476019412528891, 1)] : List FactorBlock).map factorBlockValue).prod) = 10758628645335683874353390569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_5821768747476019412528891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 10758628645335683874353390569) ^ 5379314322667841937176695284 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (23 : ZMod 10758628645335683874353390569) ^ 3586209548445227958117796856 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (23 : ZMod 10758628645335683874353390569) ^ 1536946949333669124907627224 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (23 : ZMod 10758628645335683874353390569) ^ 978057149575971261304853688 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (23 : ZMod 10758628645335683874353390569) ^ 1848 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_21517257290671367748706781123 : Nat.Prime 21517257290671367748706781123 := by
  apply lucas_primality 21517257290671367748706781123 (2 : ZMod 21517257290671367748706781123)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (433, 1), (730908757, 1), (693760829891069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (433, 1), (730908757, 1), (693760829891069, 1)] : List FactorBlock).map factorBlockValue).prod) = 21517257290671367748706781123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_433
      · exact prime_ninetyOneCK_730908757
      · exact prime_ninetyOneCK_693760829891069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21517257290671367748706781123) ^ 10758628645335683874353390561 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21517257290671367748706781123) ^ 3073893898667338249815254446 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21517257290671367748706781123) ^ 49693434851435029442740834 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21517257290671367748706781123) ^ 29439047055597621946 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 21517257290671367748706781123) ^ 31015382194538 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_21517257290671367748706781137 : Nat.Prime 21517257290671367748706781137 := by
  apply lucas_primality 21517257290671367748706781137 (10 : ZMod 21517257290671367748706781137)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (11, 1), (5821768747476019412528891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (11, 1), (5821768747476019412528891, 1)] : List FactorBlock).map factorBlockValue).prod) = 21517257290671367748706781137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_5821768747476019412528891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21517257290671367748706781137) ^ 10758628645335683874353390568 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 21517257290671367748706781137) ^ 7172419096890455916235593712 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 21517257290671367748706781137) ^ 3073893898667338249815254448 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 21517257290671367748706781137) ^ 1956114299151942522609707376 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (10 : ZMod 21517257290671367748706781137) ^ 3696 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_35862095484452279581177968559 : Nat.Prime 35862095484452279581177968559 := by
  apply lucas_primality 35862095484452279581177968559 (3 : ZMod 35862095484452279581177968559)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1229, 1), (101701, 1), (155558467, 1), (102468976117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1229, 1), (101701, 1), (155558467, 1), (102468976117, 1)] : List FactorBlock).map factorBlockValue).prod) = 35862095484452279581177968559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_1229
      · exact prime_ninetyOneCK_101701
      · exact prime_ninetyOneCK_155558467
      · exact prime_ninetyOneCK_102468976117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35862095484452279581177968559) ^ 17931047742226139790588984279 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35862095484452279581177968559) ^ 11954031828150759860392656186 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35862095484452279581177968559) ^ 29179898685477851571340902 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35862095484452279581177968559) ^ 352622840330500974239958 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35862095484452279581177968559) ^ 230537727557139526074 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35862095484452279581177968559) ^ 349980031453662774 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_53793143226678419371766952803 : Nat.Prime 53793143226678419371766952803 := by
  apply lucas_primality 53793143226678419371766952803 (2 : ZMod 53793143226678419371766952803)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1567, 1), (2085971, 1), (8228480856114563893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1567, 1), (2085971, 1), (8228480856114563893, 1)] : List FactorBlock).map factorBlockValue).prod) = 53793143226678419371766952803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_1567
      · exact prime_ninetyOneCK_2085971
      · exact prime_ninetyOneCK_8228480856114563893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53793143226678419371766952803) ^ 26896571613339209685883476401 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 53793143226678419371766952803) ^ 34328744879820305916890206 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 53793143226678419371766952803) ^ 25788059003063043240662 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (2 : ZMod 53793143226678419371766952803) ^ 6537433114 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem prime_ninetyOneCK_53793143226678419371766952841 : Nat.Prime 53793143226678419371766952841 := by
  apply lucas_primality 53793143226678419371766952841 (51 : ZMod 53793143226678419371766952841)
  · rw [← ninetyOneCKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (5821768747476019412528891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (5821768747476019412528891, 1)] : List FactorBlock).map factorBlockValue).prod) = 53793143226678419371766952841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyOneCK_2
      · exact prime_ninetyOneCK_3
      · exact prime_ninetyOneCK_5
      · exact prime_ninetyOneCK_7
      · exact prime_ninetyOneCK_11
      · exact prime_ninetyOneCK_5821768747476019412528891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (51 : ZMod 53793143226678419371766952841) ^ 26896571613339209685883476420 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (51 : ZMod 53793143226678419371766952841) ^ 17931047742226139790588984280 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (51 : ZMod 53793143226678419371766952841) ^ 10758628645335683874353390568 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (51 : ZMod 53793143226678419371766952841) ^ 7684734746668345624538136120 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (51 : ZMod 53793143226678419371766952841) ^ 4890285747879856306524268440 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide
    · change (51 : ZMod 53793143226678419371766952841) ^ 9240 ≠ 1
      rw [← ninetyOneCKFastPow_eq_pow]
      decide

private theorem phi_ninetyOneCK_107586286453356838743533905600 : Nat.totient 107586286453356838743533905600 = 41495956764122260384131686400 := by
  rw [← show ((([(2, 6), (5, 2), (31, 1), (277, 1), (7830607783084665682393, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_5, prime_ninetyOneCK_31, prime_ninetyOneCK_277, prime_ninetyOneCK_7830607783084665682393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905601 : Nat.totient 107586286453356838743533905601 = 107586282597668572109394664800 := by
  rw [← show ((([(28889209, 1), (817741039, 1), (4554130514951, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_28889209, prime_ninetyOneCK_817741039, prime_ninetyOneCK_4554130514951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905602 : Nat.totient 107586286453356838743533905602 = 33747989491796745483613324800 := by
  rw [← show ((([(2, 1), (3, 2), (17, 1), (8111, 1), (82387, 1), (526141308360718781, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_17, prime_ninetyOneCK_8111, prime_ninetyOneCK_82387, prime_ninetyOneCK_526141308360718781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905603 : Nat.totient 107586286453356838743533905603 = 82223160748688611258781990400 := by
  rw [← show ((([(7, 1), (11, 1), (53, 1), (5023, 1), (6983, 1), (208631, 1), (3602518855597, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_7, prime_ninetyOneCK_11, prime_ninetyOneCK_53, prime_ninetyOneCK_5023, prime_ninetyOneCK_6983, prime_ninetyOneCK_208631, prime_ninetyOneCK_3602518855597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905604 : Nat.totient 107586286453356838743533905604 = 53758788710196557708502691680 := by
  rw [← show ((([(2, 2), (1567, 1), (2085971, 1), (8228480856114563893, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_1567, prime_ninetyOneCK_2085971, prime_ninetyOneCK_8228480856114563893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905605 : Nat.totient 107586286453356838743533905605 = 57379351671237437789771236608 := by
  rw [← show ((([(3, 1), (5, 1), (51979409, 1), (137985776192462209723, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_5, prime_ninetyOneCK_51979409, prime_ninetyOneCK_137985776192462209723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905606 : Nat.totient 107586286453356838743533905606 = 53793143226678419371766952802 := by
  rw [← show ((([(2, 1), (53793143226678419371766952803, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_53793143226678419371766952803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905607 : Nat.totient 107586286453356838743533905607 = 107174894780789684305129303488 := by
  rw [← show ((([(283, 1), (3433, 1), (110738000691024074940413, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_283, prime_ninetyOneCK_3433, prime_ninetyOneCK_110738000691024074940413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905608 : Nat.totient 107586286453356838743533905608 = 35862095484400142761766525888 := by
  rw [← show ((([(2, 3), (3, 1), (687918475733, 1), (6516414507954599, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_687918475733, prime_ninetyOneCK_6516414507954599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905609 : Nat.totient 107586286453356838743533905609 = 100013029606261227555484729344 := by
  rw [← show ((([(23, 1), (83, 1), (89, 1), (307, 1), (547, 1), (36277, 1), (103945074633473, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_23, prime_ninetyOneCK_83, prime_ninetyOneCK_89, prime_ninetyOneCK_307, prime_ninetyOneCK_547, prime_ninetyOneCK_36277, prime_ninetyOneCK_103945074633473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905610 : Nat.totient 107586286453356838743533905610 = 36801537988198017053558827008 := by
  rw [← show ((([(2, 1), (5, 1), (7, 2), (433, 1), (730908757, 1), (693760829891069, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_5, prime_ninetyOneCK_7, prime_ninetyOneCK_433, prime_ninetyOneCK_730908757, prime_ninetyOneCK_693760829891069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905611 : Nat.totient 107586286453356838743533905611 = 66199910515030870228913011200 := by
  rw [← show ((([(3, 2), (13, 1), (9421, 1), (8942803, 1), (10914413112776441, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_13, prime_ninetyOneCK_9421, prime_ninetyOneCK_8942803, prime_ninetyOneCK_10914413112776441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905612 : Nat.totient 107586286453356838743533905612 = 50961924337359563728711129296 := by
  rw [← show ((([(2, 2), (19, 1), (61790243, 1), (22909912043573142059, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_19, prime_ninetyOneCK_61790243, prime_ninetyOneCK_22909912043573142059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905613 : Nat.totient 107586286453356838743533905613 = 103876414506689361545481012288 := by
  rw [← show ((([(29, 1), (3709871946667477198052893297, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_29, prime_ninetyOneCK_3709871946667477198052893297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905614 : Nat.totient 107586286453356838743533905614 = 32187694118575892163965574240 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (79, 1), (21059, 1), (979824164474184004739, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_11, prime_ninetyOneCK_79, prime_ninetyOneCK_21059, prime_ninetyOneCK_979824164474184004739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905615 : Nat.totient 107586286453356838743533905615 = 86069029162685470994827124488 := by
  rw [← show ((([(5, 1), (21517257290671367748706781123, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_5, prime_ninetyOneCK_21517257290671367748706781123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905616 : Nat.totient 107586286453356838743533905616 = 53793143043592448638314721536 := by
  rw [← show ((([(2, 4), (293813573, 1), (22885746341387715337, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_293813573, prime_ninetyOneCK_22885746341387715337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905617 : Nat.totient 107586286453356838743533905617 = 61477657860648481733962137600 := by
  rw [← show ((([(3, 1), (7, 1), (284857, 1), (14321921, 1), (1255768117282741, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_7, prime_ninetyOneCK_284857, prime_ninetyOneCK_14321921, prime_ninetyOneCK_1255768117282741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905618 : Nat.totient 107586286453356838743533905618 = 53676455280416644058596091280 := by
  rw [← show ((([(2, 1), (461, 1), (116687946261775313170861069, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_461, prime_ninetyOneCK_116687946261775313170861069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905619 : Nat.totient 107586286453356838743533905619 = 101257677714575788584090849792 := by
  rw [← show ((([(17, 1), (28758187, 1), (767495077, 1), (286728520693, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_17, prime_ninetyOneCK_28758187, prime_ninetyOneCK_767495077, prime_ninetyOneCK_286728520693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905620 : Nat.totient 107586286453356838743533905620 = 28670382724893658349767350912 := by
  rw [← show ((([(2, 2), (3, 3), (5, 1), (1487, 1), (133983768528925799825069, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_5, prime_ninetyOneCK_1487, prime_ninetyOneCK_133983768528925799825069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905621 : Nat.totient 107586286453356838743533905621 = 107502821529808850505563746144 := by
  rw [← show ((([(1289, 1), (83464923547988237970158189, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_1289, prime_ninetyOneCK_83464923547988237970158189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905622 : Nat.totient 107586286453356838743533905622 = 53686198607894616086918040192 := by
  rw [← show ((([(2, 1), (503, 1), (1270556105873, 1), (84171504309469, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_503, prime_ninetyOneCK_1270556105873, prime_ninetyOneCK_84171504309469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905623 : Nat.totient 107586286453356838743533905623 = 71634079324758786782251543680 := by
  rw [← show ((([(3, 1), (821, 1), (26053, 1), (1676620476794038255157, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_821, prime_ninetyOneCK_26053, prime_ninetyOneCK_1676620476794038255157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905624 : Nat.totient 107586286453356838743533905624 = 42250503901257859340715540480 := by
  rw [← show ((([(2, 3), (7, 1), (13, 1), (137, 1), (97127, 1), (170108047, 1), (65289018161, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_7, prime_ninetyOneCK_13, prime_ninetyOneCK_137, prime_ninetyOneCK_97127, prime_ninetyOneCK_170108047, prime_ninetyOneCK_65289018161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905625 : Nat.totient 107586286453356838743533905625 = 76961874064994459905955400000 := by
  rw [← show ((([(5, 4), (11, 1), (61, 1), (256539580216648199686519, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_5, prime_ninetyOneCK_11, prime_ninetyOneCK_61, prime_ninetyOneCK_256539580216648199686519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905626 : Nat.totient 107586286453356838743533905626 = 35862033935644599811784877360 := by
  rw [← show ((([(2, 1), (3, 1), (985723, 1), (1424947, 1), (12765918439437391, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_985723, prime_ninetyOneCK_1424947, prime_ninetyOneCK_12765918439437391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905627 : Nat.totient 107586286453356838743533905627 = 107509929968388273795974360064 := by
  rw [← show ((([(1409, 1), (174718218797, 1), (437026458252199, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_1409, prime_ninetyOneCK_174718218797, prime_ninetyOneCK_437026458252199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905628 : Nat.totient 107586286453356838743533905628 = 53755604396792391165645688992 := by
  rw [← show ((([(2, 2), (1433, 1), (18769414943014103060630479, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_1433, prime_ninetyOneCK_18769414943014103060630479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905629 : Nat.totient 107586286453356838743533905629 = 71013724996894063628808060000 := by
  rw [← show ((([(3, 2), (101, 1), (218191, 1), (542445613126892949791, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_101, prime_ninetyOneCK_218191, prime_ninetyOneCK_542445613126892949791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905630 : Nat.totient 107586286453356838743533905630 = 43030709984593619495234766336 := by
  rw [← show ((([(2, 1), (5, 1), (11317, 1), (22028423, 1), (43156100318554193, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_5, prime_ninetyOneCK_11317, prime_ninetyOneCK_22028423, prime_ninetyOneCK_43156100318554193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905631 : Nat.totient 107586286453356838743533905631 = 82479147590040444763818854400 := by
  rw [← show ((([(7, 1), (19, 1), (31, 1), (41, 1), (21139, 1), (23911417, 1), (1259128266559, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_7, prime_ninetyOneCK_19, prime_ninetyOneCK_31, prime_ninetyOneCK_41, prime_ninetyOneCK_21139, prime_ninetyOneCK_23911417, prime_ninetyOneCK_1259128266559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905632 : Nat.totient 107586286453356838743533905632 = 32484494440386499049462956032 := by
  rw [← show ((([(2, 5), (3, 1), (23, 1), (37, 1), (43, 1), (349, 1), (1499, 1), (136756897, 1), (428066627, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_23, prime_ninetyOneCK_37, prime_ninetyOneCK_43, prime_ninetyOneCK_349, prime_ninetyOneCK_1499, prime_ninetyOneCK_136756897, prime_ninetyOneCK_428066627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905633 : Nat.totient 107586286453356838743533905633 = 106541759400411626716897654020 := by
  rw [← show ((([(103, 1), (1044527052945212026636251511, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_103, prime_ninetyOneCK_1044527052945212026636251511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905634 : Nat.totient 107586286453356838743533905634 = 52876315472071890114008894592 := by
  rw [← show ((([(2, 1), (59, 1), (10463, 1), (2079193, 1), (41910600189347557, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_59, prime_ninetyOneCK_10463, prime_ninetyOneCK_2079193, prime_ninetyOneCK_41910600189347557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905635 : Nat.totient 107586286453356838743533905635 = 56994256447773824193442568960 := by
  rw [← show ((([(3, 1), (5, 1), (149, 1), (48137040918727892055272441, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_5, prime_ninetyOneCK_149, prime_ninetyOneCK_48137040918727892055272441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905636 : Nat.totient 107586286453356838743533905636 = 45825228417972884927269294080 := by
  rw [← show ((([(2, 2), (11, 1), (17, 1), (229, 1), (18108697, 1), (34684276123898839, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_11, prime_ninetyOneCK_17, prime_ninetyOneCK_229, prime_ninetyOneCK_18108697, prime_ninetyOneCK_34684276123898839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905637 : Nat.totient 107586286453356838743533905637 = 98993126988797850199588609152 := by
  rw [← show ((([(13, 1), (313, 1), (17694779, 1), (1494252821489830387, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_13, prime_ninetyOneCK_313, prime_ninetyOneCK_17694779, prime_ninetyOneCK_1494252821489830387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905638 : Nat.totient 107586286453356838743533905638 = 30598456450538766083107968000 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (241, 1), (3331, 1), (8171, 1), (130172572147740893, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_7, prime_ninetyOneCK_241, prime_ninetyOneCK_3331, prime_ninetyOneCK_8171, prime_ninetyOneCK_130172572147740893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905639 : Nat.totient 107586286453356838743533905639 = 107045320078864611778825687680 := by
  rw [← show ((([(199, 1), (376759, 1), (2246641, 1), (638714131623319, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_199, prime_ninetyOneCK_376759, prime_ninetyOneCK_2246641, prime_ninetyOneCK_638714131623319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905640 : Nat.totient 107586286453356838743533905640 = 42854453805875189126518347520 := by
  rw [← show ((([(2, 3), (5, 1), (239, 1), (952285781, 1), (11817666375632699, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_5, prime_ninetyOneCK_239, prime_ninetyOneCK_952285781, prime_ninetyOneCK_11817666375632699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905641 : Nat.totient 107586286453356838743533905641 = 71633054752605581319337461264 := by
  rw [← show ((([(3, 1), (787, 1), (5007398047, 1), (9100155523698223, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_787, prime_ninetyOneCK_5007398047, prime_ninetyOneCK_9100155523698223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905642 : Nat.totient 107586286453356838743533905642 = 51638667412684232455330295232 := by
  rw [← show ((([(2, 1), (29, 1), (179, 1), (5527, 1), (1374187, 1), (1364396486603519, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_29, prime_ninetyOneCK_179, prime_ninetyOneCK_5527, prime_ninetyOneCK_1374187, prime_ninetyOneCK_1364396486603519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905643 : Nat.totient 107586286453356838743533905643 = 107013796342641711343985580000 := by
  rw [← show ((([(191, 1), (11701, 1), (1655531, 1), (29077914370827683, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_191, prime_ninetyOneCK_11701, prime_ninetyOneCK_1655531, prime_ninetyOneCK_29077914370827683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905644 : Nat.totient 107586286453356838743533905644 = 35862095484452279581177968544 := by
  rw [← show ((([(2, 2), (3, 1), (8965523871113069895294492137, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_8965523871113069895294492137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905645 : Nat.totient 107586286453356838743533905645 = 72031259526557848986158984448 := by
  rw [← show ((([(5, 1), (7, 1), (47, 1), (419, 1), (324503, 1), (481014619213032493, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_5, prime_ninetyOneCK_7, prime_ninetyOneCK_47, prime_ninetyOneCK_419, prime_ninetyOneCK_324503, prime_ninetyOneCK_481014619213032493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905646 : Nat.totient 107586286453356838743533905646 = 53793143019208904889342901528 := by
  rw [← show ((([(2, 1), (259282157, 1), (207469514482164769139, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_259282157, prime_ninetyOneCK_207469514482164769139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905647 : Nat.totient 107586286453356838743533905647 = 65203555054264728934732704000 := by
  rw [← show ((([(3, 4), (11, 1), (255851, 1), (978772519, 1), (482181259793, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_11, prime_ninetyOneCK_255851, prime_ninetyOneCK_978772519, prime_ninetyOneCK_482181259793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905648 : Nat.totient 107586286453356838743533905648 = 53035493320493439879670982400 := by
  rw [← show ((([(2, 4), (71, 1), (33485042333, 1), (2828314718354221, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_71, prime_ninetyOneCK_33485042333, prime_ninetyOneCK_2828314718354221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905649 : Nat.totient 107586286453356838743533905649 = 106421433904856947990143787008 := by
  rw [← show ((([(173, 1), (197, 1), (1511697906673, 1), (2088235989473, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_173, prime_ninetyOneCK_197, prime_ninetyOneCK_1511697906673, prime_ninetyOneCK_2088235989473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905650 : Nat.totient 107586286453356838743533905650 = 25069603941916745493230161920 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (13, 1), (19, 1), (1297, 1), (2238869236353733129469, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_5, prime_ninetyOneCK_13, prime_ninetyOneCK_19, prime_ninetyOneCK_1297, prime_ninetyOneCK_2238869236353733129469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905651 : Nat.totient 107586286453356838743533905651 = 107585325481669781881675700160 := by
  rw [← show ((([(111959, 1), (3832847929, 1), (250712690703341, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_111959, prime_ninetyOneCK_3832847929, prime_ninetyOneCK_250712690703341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905652 : Nat.totient 107586286453356838743533905652 = 46103947958729236940249179392 := by
  rw [← show ((([(2, 2), (7, 1), (10337, 1), (371710106736400581626107, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_7, prime_ninetyOneCK_10337, prime_ninetyOneCK_371710106736400581626107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905653 : Nat.totient 107586286453356838743533905653 = 67496084887302672708001370112 := by
  rw [← show ((([(3, 1), (17, 1), (7907, 1), (135409, 1), (426587507, 1), (4618695583, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_17, prime_ninetyOneCK_7907, prime_ninetyOneCK_135409, prime_ninetyOneCK_426587507, prime_ninetyOneCK_4618695583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905654 : Nat.totient 107586286453356838743533905654 = 53067081629242010857879113984 := by
  rw [← show ((([(2, 1), (109, 1), (293, 1), (1049, 1), (1605673778290762660979, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_109, prime_ninetyOneCK_293, prime_ninetyOneCK_1049, prime_ninetyOneCK_1605673778290762660979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905655 : Nat.totient 107586286453356838743533905655 = 82006392419045596892812804096 := by
  rw [← show ((([(5, 1), (23, 1), (257, 1), (491297, 1), (7409379533160921293, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_5, prime_ninetyOneCK_23, prime_ninetyOneCK_257, prime_ninetyOneCK_491297, prime_ninetyOneCK_7409379533160921293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905656 : Nat.totient 107586286453356838743533905656 = 34856616061026762159343739904 := by
  rw [← show ((([(2, 3), (3, 2), (53, 1), (107, 1), (314654917, 1), (837394782914189, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_53, prime_ninetyOneCK_107, prime_ninetyOneCK_314654917, prime_ninetyOneCK_837394782914189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905657 : Nat.totient 107586286453356838743533905657 = 107203045273002525325248000000 := by
  rw [← show ((([(281, 1), (288467, 1), (530640001, 1), (2501234868091, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_281, prime_ninetyOneCK_288467, prime_ninetyOneCK_530640001, prime_ninetyOneCK_2501234868091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905658 : Nat.totient 107586286453356838743533905658 = 48902857478798563065242684380 := by
  rw [← show ((([(2, 1), (11, 1), (4890285747879856306524268439, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_11, prime_ninetyOneCK_4890285747879856306524268439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905659 : Nat.totient 107586286453356838743533905659 = 60622532215373340423781194240 := by
  rw [← show ((([(3, 1), (7, 2), (139, 1), (167, 1), (1321, 1), (36767, 1), (649153343668267, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_7, prime_ninetyOneCK_139, prime_ninetyOneCK_167, prime_ninetyOneCK_1321, prime_ninetyOneCK_36767, prime_ninetyOneCK_649153343668267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905660 : Nat.totient 107586286453356838743533905660 = 43034514581342735497413562256 := by
  rw [← show ((([(2, 2), (5, 1), (5379314322667841937176695283, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_5, prime_ninetyOneCK_5379314322667841937176695283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905661 : Nat.totient 107586286453356838743533905661 = 107578913978176946471673741312 := by
  rw [← show ((([(14593, 1), (6438090829, 1), (1145131167897713, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_14593, prime_ninetyOneCK_6438090829, prime_ninetyOneCK_1145131167897713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905662 : Nat.totient 107586286453356838743533905662 = 34696401312382412599420070400 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (3967, 1), (355171, 1), (5592817, 1), (73402975543, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_31, prime_ninetyOneCK_3967, prime_ninetyOneCK_355171, prime_ninetyOneCK_5592817, prime_ninetyOneCK_73402975543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905663 : Nat.totient 107586286453356838743533905663 = 97321268598145640361044582400 := by
  rw [← show ((([(13, 1), (67, 1), (193, 1), (4251461, 1), (150536998912485461, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_13, prime_ninetyOneCK_67, prime_ninetyOneCK_193, prime_ninetyOneCK_4251461, prime_ninetyOneCK_150536998912485461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905664 : Nat.totient 107586286453356838743533905664 = 53793143226678419371766952704 := by
  rw [← show ((([(2, 8), (420258931458425151341929319, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_420258931458425151341929319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905665 : Nat.totient 107586286453356838743533905665 = 57198345353120102701083843840 := by
  rw [← show ((([(3, 2), (5, 1), (317, 1), (7541975916814359533370761, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_5, prime_ninetyOneCK_317, prime_ninetyOneCK_7541975916814359533370761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905666 : Nat.totient 107586286453356838743533905666 = 46108364194525015202044007664 := by
  rw [← show ((([(2, 1), (7, 1), (1041163, 1), (7380914176424196427013, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_7, prime_ninetyOneCK_1041163, prime_ninetyOneCK_7380914176424196427013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905667 : Nat.totient 107586286453356838743533905667 = 106112241522814500898969881600 := by
  rw [← show ((([(73, 1), (444461, 1), (13924957, 1), (13978967, 1), (17034581, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_73, prime_ninetyOneCK_444461, prime_ninetyOneCK_13924957, prime_ninetyOneCK_13978967, prime_ninetyOneCK_17034581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905668 : Nat.totient 107586286453356838743533905668 = 35860751378328654069406144960 := by
  rw [← show ((([(2, 2), (3, 1), (26681, 1), (336026530906377942929219, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_26681, prime_ninetyOneCK_336026530906377942929219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905669 : Nat.totient 107586286453356838743533905669 = 90092918904398975611538668800 := by
  rw [← show ((([(11, 1), (19, 1), (37, 1), (2221, 1), (4447, 1), (1408617952566685739, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_11, prime_ninetyOneCK_19, prime_ninetyOneCK_37, prime_ninetyOneCK_2221, prime_ninetyOneCK_4447, prime_ninetyOneCK_1408617952566685739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905670 : Nat.totient 107586286453356838743533905670 = 40503003723927092233632153600 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (589451, 1), (368237953, 1), (2915625496517, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_5, prime_ninetyOneCK_17, prime_ninetyOneCK_589451, prime_ninetyOneCK_368237953, prime_ninetyOneCK_2915625496517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905671 : Nat.totient 107586286453356838743533905671 = 68809853939680169777375416320 := by
  rw [← show ((([(3, 1), (29, 1), (157, 1), (268963109, 1), (29285004561828641, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_29, prime_ninetyOneCK_157, prime_ninetyOneCK_268963109, prime_ninetyOneCK_29285004561828641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905672 : Nat.totient 107586286453356838743533905672 = 52480997263254270473661888000 := by
  rw [← show ((([(2, 3), (41, 1), (725077, 1), (1148387, 1), (393922399632551, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_41, prime_ninetyOneCK_725077, prime_ninetyOneCK_1148387, prime_ninetyOneCK_393922399632551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905673 : Nat.totient 107586286453356838743533905673 = 92184349082946364202639578560 := by
  rw [← show ((([(7, 1), (2887, 1), (175411, 1), (371099383, 1), (81783376469, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_7, prime_ninetyOneCK_2887, prime_ninetyOneCK_175411, prime_ninetyOneCK_371099383, prime_ninetyOneCK_81783376469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905674 : Nat.totient 107586286453356838743533905674 = 35832563019147401492013100800 := by
  rw [← show ((([(2, 1), (3, 3), (1229, 1), (101701, 1), (155558467, 1), (102468976117, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_1229, prime_ninetyOneCK_101701, prime_ninetyOneCK_155558467, prime_ninetyOneCK_102468976117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905675 : Nat.totient 107586286453356838743533905675 = 83425687773524351434716045600 := by
  rw [← show ((([(5, 2), (43, 1), (131, 1), (763971499757549005812419, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_5, prime_ninetyOneCK_43, prime_ninetyOneCK_131, prime_ninetyOneCK_763971499757549005812419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905676 : Nat.totient 107586286453356838743533905676 = 49651457899451225996778362880 := by
  rw [← show ((([(2, 2), (13, 1), (13241, 1), (44226257, 1), (3533072934144599, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_13, prime_ninetyOneCK_13241, prime_ninetyOneCK_44226257, prime_ninetyOneCK_3533072934144599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905677 : Nat.totient 107586286453356838743533905677 = 71724190968904559162355937116 := by
  rw [← show ((([(3, 1), (35862095484452279581177968559, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_35862095484452279581177968559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905678 : Nat.totient 107586286453356838743533905678 = 51454242546191429155756166776 := by
  rw [← show ((([(2, 1), (23, 1), (752627, 1), (3107558344576276878059, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_23, prime_ninetyOneCK_752627, prime_ninetyOneCK_3107558344576276878059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905679 : Nat.totient 107586286453356838743533905679 = 107449264456835883661096133760 := by
  rw [← show ((([(797, 1), (52861, 1), (498877723, 1), (5118811181269, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_797, prime_ninetyOneCK_52861, prime_ninetyOneCK_498877723, prime_ninetyOneCK_5118811181269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905680 : Nat.totient 107586286453356838743533905680 = 22355591990307914544110937600 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (5821768747476019412528891, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_5, prime_ninetyOneCK_7, prime_ninetyOneCK_11, prime_ninetyOneCK_5821768747476019412528891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905681 : Nat.totient 107586286453356838743533905681 = 107585351169879650676720971808 := by
  rw [← show ((([(115337, 1), (43310299, 1), (21537588965206187, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_115337, prime_ninetyOneCK_43310299, prime_ninetyOneCK_21537588965206187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905682 : Nat.totient 107586286453356838743533905682 = 53793143226678419371766952840 := by
  rw [← show ((([(2, 1), (53793143226678419371766952841, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_53793143226678419371766952841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905683 : Nat.totient 107586286453356838743533905683 = 71715497006319153772973284800 := by
  rw [← show ((([(3, 2), (9323, 1), (71693, 1), (187834483, 1), (95215279351, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_9323, prime_ninetyOneCK_71693, prime_ninetyOneCK_187834483, prime_ninetyOneCK_95215279351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905684 : Nat.totient 107586286453356838743533905684 = 53790448314438217056283131200 := by
  rw [← show ((([(2, 2), (19961, 1), (1347456120101157741890861, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_19961, prime_ninetyOneCK_1347456120101157741890861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905685 : Nat.totient 107586286453356838743533905685 = 86069029162685470994827124544 := by
  rw [← show ((([(5, 1), (21517257290671367748706781137, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_5, prime_ninetyOneCK_21517257290671367748706781137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905686 : Nat.totient 107586286453356838743533905686 = 35274192240372628346898101280 := by
  rw [← show ((([(2, 1), (3, 1), (61, 1), (894909319, 1), (328470825021742859, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_61, prime_ninetyOneCK_894909319, prime_ninetyOneCK_328470825021742859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905687 : Nat.totient 107586286453356838743533905687 = 86217511509233600392313395200 := by
  rw [← show ((([(7, 1), (17, 1), (151, 1), (25557079, 1), (234272759512696337, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_7, prime_ninetyOneCK_17, prime_ninetyOneCK_151, prime_ninetyOneCK_25557079, prime_ninetyOneCK_234272759512696337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905688 : Nat.totient 107586286453356838743533905688 = 50560638752089219531257446400 := by
  rw [← show ((([(2, 3), (19, 1), (127, 1), (4477391, 1), (534427681, 1), (2329140257, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_19, prime_ninetyOneCK_127, prime_ninetyOneCK_4477391, prime_ninetyOneCK_534427681, prime_ninetyOneCK_2329140257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905689 : Nat.totient 107586286453356838743533905689 = 66021002725212509133022670592 := by
  rw [← show ((([(3, 1), (13, 1), (367, 1), (12983, 1), (144539, 1), (4005586762814069, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_13, prime_ninetyOneCK_367, prime_ninetyOneCK_12983, prime_ninetyOneCK_144539, prime_ninetyOneCK_4005586762814069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905690 : Nat.totient 107586286453356838743533905690 = 43034514581342735497413562272 := by
  rw [← show ((([(2, 1), (5, 1), (10758628645335683874353390569, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_5, prime_ninetyOneCK_10758628645335683874353390569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905691 : Nat.totient 107586286453356838743533905691 = 97799500932160562257131828000 := by
  rw [← show ((([(11, 1), (15923, 1), (1373027, 1), (315837031, 1), (1416436831, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_11, prime_ninetyOneCK_15923, prime_ninetyOneCK_1373027, prime_ninetyOneCK_315837031, prime_ninetyOneCK_1416436831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905692 : Nat.totient 107586286453356838743533905692 = 34221572612157501298565038080 := by
  rw [← show ((([(2, 2), (3, 2), (47, 1), (83, 1), (97, 1), (397, 1), (3203, 1), (6210967925708461, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_47, prime_ninetyOneCK_83, prime_ninetyOneCK_97, prime_ninetyOneCK_397, prime_ninetyOneCK_3203, prime_ninetyOneCK_6210967925708461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905693 : Nat.totient 107586286453356838743533905693 = 101028735857926141900364471040 := by
  rw [← show ((([(31, 1), (59, 1), (79, 1), (4637, 1), (20479, 1), (2459659, 1), (3187831639, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_31, prime_ninetyOneCK_59, prime_ninetyOneCK_79, prime_ninetyOneCK_4637, prime_ninetyOneCK_20479, prime_ninetyOneCK_2459659, prime_ninetyOneCK_3187831639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905694 : Nat.totient 107586286453356838743533905694 = 45930384530358341626644323328 := by
  rw [← show ((([(2, 1), (7, 1), (457, 1), (739, 1), (3089, 1), (7366315822800385643, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_7, prime_ninetyOneCK_457, prime_ninetyOneCK_739, prime_ninetyOneCK_3089, prime_ninetyOneCK_7366315822800385643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905695 : Nat.totient 107586286453356838743533905695 = 57374912641693706390598804992 := by
  rw [← show ((([(3, 1), (5, 1), (12923, 1), (1508440883, 1), (367937471391857, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_5, prime_ninetyOneCK_12923, prime_ninetyOneCK_1508440883, prime_ninetyOneCK_367937471391857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905696 : Nat.totient 107586286453356838743533905696 = 53690142684050571513881364480 := by
  rw [← show ((([(2, 5), (643, 1), (2777, 1), (660275071, 1), (2851643202613, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_643, prime_ninetyOneCK_2777, prime_ninetyOneCK_660275071, prime_ninetyOneCK_2851643202613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905697 : Nat.totient 107586286453356838743533905697 = 107539732456622370185012253060 := by
  rw [← show ((([(2311, 1), (46553996734468558521650327, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2311, prime_ninetyOneCK_46553996734468558521650327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905698 : Nat.totient 107586286453356838743533905698 = 35459134979697516214218291200 := by
  rw [← show ((([(2, 1), (3, 1), (89, 1), (2563079, 1), (19953701, 1), (3939401153393, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_3, prime_ninetyOneCK_89, prime_ninetyOneCK_2563079, prime_ninetyOneCK_19953701, prime_ninetyOneCK_3939401153393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905699 : Nat.totient 107586286453356838743533905699 = 107087858245593969625763068680 := by
  rw [← show ((([(223, 1), (6703, 1), (71975192456732002565971, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_223, prime_ninetyOneCK_6703, prime_ninetyOneCK_71975192456732002565971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905700 : Nat.totient 107586286453356838743533905700 = 41550565802675744618192403840 := by
  rw [← show ((([(2, 2), (5, 2), (29, 1), (37098719466674771980528933, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_2, prime_ninetyOneCK_5, prime_ninetyOneCK_29, prime_ninetyOneCK_37098719466674771980528933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyOneCK_107586286453356838743533905701 : Nat.totient 107586286453356838743533905701 = 58804880657750649748151274240 := by
  rw [← show ((([(3, 3), (7, 1), (23, 1), (1277597, 1), (852018269, 1), (22736545831, 1)] : List FactorBlock).map factorBlockValue).prod) = 107586286453356838743533905701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyOneCK_3, prime_ninetyOneCK_7, prime_ninetyOneCK_23, prime_ninetyOneCK_1277597, prime_ninetyOneCK_852018269, prime_ninetyOneCK_22736545831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetyOneCK : certifiedKill 1 107586286453356838743533905599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetyOneCK_107586286453356838743533905600, phi_ninetyOneCK_107586286453356838743533905601, phi_ninetyOneCK_107586286453356838743533905602,
    phi_ninetyOneCK_107586286453356838743533905603, phi_ninetyOneCK_107586286453356838743533905604, phi_ninetyOneCK_107586286453356838743533905605,
    phi_ninetyOneCK_107586286453356838743533905606, phi_ninetyOneCK_107586286453356838743533905607, phi_ninetyOneCK_107586286453356838743533905608,
    phi_ninetyOneCK_107586286453356838743533905609, phi_ninetyOneCK_107586286453356838743533905610, phi_ninetyOneCK_107586286453356838743533905611,
    phi_ninetyOneCK_107586286453356838743533905612, phi_ninetyOneCK_107586286453356838743533905613, phi_ninetyOneCK_107586286453356838743533905614,
    phi_ninetyOneCK_107586286453356838743533905615, phi_ninetyOneCK_107586286453356838743533905616, phi_ninetyOneCK_107586286453356838743533905617,
    phi_ninetyOneCK_107586286453356838743533905618, phi_ninetyOneCK_107586286453356838743533905619, phi_ninetyOneCK_107586286453356838743533905620,
    phi_ninetyOneCK_107586286453356838743533905621, phi_ninetyOneCK_107586286453356838743533905622, phi_ninetyOneCK_107586286453356838743533905623,
    phi_ninetyOneCK_107586286453356838743533905624, phi_ninetyOneCK_107586286453356838743533905625, phi_ninetyOneCK_107586286453356838743533905626,
    phi_ninetyOneCK_107586286453356838743533905627, phi_ninetyOneCK_107586286453356838743533905628, phi_ninetyOneCK_107586286453356838743533905629,
    phi_ninetyOneCK_107586286453356838743533905630, phi_ninetyOneCK_107586286453356838743533905631, phi_ninetyOneCK_107586286453356838743533905632,
    phi_ninetyOneCK_107586286453356838743533905633, phi_ninetyOneCK_107586286453356838743533905634, phi_ninetyOneCK_107586286453356838743533905635,
    phi_ninetyOneCK_107586286453356838743533905636, phi_ninetyOneCK_107586286453356838743533905637, phi_ninetyOneCK_107586286453356838743533905638,
    phi_ninetyOneCK_107586286453356838743533905639, phi_ninetyOneCK_107586286453356838743533905640, phi_ninetyOneCK_107586286453356838743533905641,
    phi_ninetyOneCK_107586286453356838743533905642, phi_ninetyOneCK_107586286453356838743533905643, phi_ninetyOneCK_107586286453356838743533905644,
    phi_ninetyOneCK_107586286453356838743533905645, phi_ninetyOneCK_107586286453356838743533905646, phi_ninetyOneCK_107586286453356838743533905647,
    phi_ninetyOneCK_107586286453356838743533905648, phi_ninetyOneCK_107586286453356838743533905649, phi_ninetyOneCK_107586286453356838743533905650,
    phi_ninetyOneCK_107586286453356838743533905651, phi_ninetyOneCK_107586286453356838743533905652, phi_ninetyOneCK_107586286453356838743533905653,
    phi_ninetyOneCK_107586286453356838743533905654, phi_ninetyOneCK_107586286453356838743533905655, phi_ninetyOneCK_107586286453356838743533905656,
    phi_ninetyOneCK_107586286453356838743533905657, phi_ninetyOneCK_107586286453356838743533905658, phi_ninetyOneCK_107586286453356838743533905659,
    phi_ninetyOneCK_107586286453356838743533905660, phi_ninetyOneCK_107586286453356838743533905661, phi_ninetyOneCK_107586286453356838743533905662,
    phi_ninetyOneCK_107586286453356838743533905663, phi_ninetyOneCK_107586286453356838743533905664, phi_ninetyOneCK_107586286453356838743533905665,
    phi_ninetyOneCK_107586286453356838743533905666, phi_ninetyOneCK_107586286453356838743533905667, phi_ninetyOneCK_107586286453356838743533905668,
    phi_ninetyOneCK_107586286453356838743533905669, phi_ninetyOneCK_107586286453356838743533905670, phi_ninetyOneCK_107586286453356838743533905671,
    phi_ninetyOneCK_107586286453356838743533905672, phi_ninetyOneCK_107586286453356838743533905673, phi_ninetyOneCK_107586286453356838743533905674,
    phi_ninetyOneCK_107586286453356838743533905675, phi_ninetyOneCK_107586286453356838743533905676, phi_ninetyOneCK_107586286453356838743533905677,
    phi_ninetyOneCK_107586286453356838743533905678, phi_ninetyOneCK_107586286453356838743533905679, phi_ninetyOneCK_107586286453356838743533905680,
    phi_ninetyOneCK_107586286453356838743533905681, phi_ninetyOneCK_107586286453356838743533905682, phi_ninetyOneCK_107586286453356838743533905683,
    phi_ninetyOneCK_107586286453356838743533905684, phi_ninetyOneCK_107586286453356838743533905685, phi_ninetyOneCK_107586286453356838743533905686,
    phi_ninetyOneCK_107586286453356838743533905687, phi_ninetyOneCK_107586286453356838743533905688, phi_ninetyOneCK_107586286453356838743533905689,
    phi_ninetyOneCK_107586286453356838743533905690, phi_ninetyOneCK_107586286453356838743533905691, phi_ninetyOneCK_107586286453356838743533905692,
    phi_ninetyOneCK_107586286453356838743533905693, phi_ninetyOneCK_107586286453356838743533905694, phi_ninetyOneCK_107586286453356838743533905695,
    phi_ninetyOneCK_107586286453356838743533905696, phi_ninetyOneCK_107586286453356838743533905697, phi_ninetyOneCK_107586286453356838743533905698,
    phi_ninetyOneCK_107586286453356838743533905699, phi_ninetyOneCK_107586286453356838743533905700, phi_ninetyOneCK_107586286453356838743533905701
    ]

end TotientTailPeriodKiller
end Erdos249257
