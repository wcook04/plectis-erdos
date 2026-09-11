import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtyNineEGFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtyNineEGFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtyNineEGFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtyNineEGFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtyNineEGFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtyNineEGFastPow a n * oneHundredThirtyNineEGFastPow a n * a else oneHundredThirtyNineEGFastPow a n * oneHundredThirtyNineEGFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtyNineEG_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtyNineEG_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtyNineEG_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtyNineEG_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtyNineEG_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtyNineEG_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtyNineEG_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtyNineEG_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtyNineEG_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtyNineEG_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtyNineEG_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtyNineEG_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtyNineEG_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtyNineEG_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtyNineEG_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtyNineEG_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtyNineEG_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtyNineEG_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtyNineEG_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtyNineEG_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtyNineEG_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtyNineEG_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtyNineEG_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtyNineEG_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtyNineEG_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtyNineEG_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtyNineEG_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtyNineEG_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtyNineEG_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtyNineEG_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtyNineEG_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirtyNineEG_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirtyNineEG_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtyNineEG_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThirtyNineEG_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtyNineEG_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtyNineEG_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtyNineEG_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtyNineEG_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtyNineEG_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredThirtyNineEG_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThirtyNineEG_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtyNineEG_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirtyNineEG_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtyNineEG_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirtyNineEG_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirtyNineEG_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredThirtyNineEG_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThirtyNineEG_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtyNineEG_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirtyNineEG_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirtyNineEG_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirtyNineEG_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredThirtyNineEG_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredThirtyNineEG_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThirtyNineEG_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtyNineEG_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThirtyNineEG_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredThirtyNineEG_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredThirtyNineEG_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirtyNineEG_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredThirtyNineEG_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredThirtyNineEG_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredThirtyNineEG_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirtyNineEG_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredThirtyNineEG_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredThirtyNineEG_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredThirtyNineEG_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredThirtyNineEG_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredThirtyNineEG_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThirtyNineEG_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredThirtyNineEG_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredThirtyNineEG_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredThirtyNineEG_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredThirtyNineEG_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredThirtyNineEG_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredThirtyNineEG_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredThirtyNineEG_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredThirtyNineEG_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredThirtyNineEG_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredThirtyNineEG_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredThirtyNineEG_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredThirtyNineEG_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredThirtyNineEG_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredThirtyNineEG_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredThirtyNineEG_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredThirtyNineEG_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredThirtyNineEG_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredThirtyNineEG_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredThirtyNineEG_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredThirtyNineEG_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredThirtyNineEG_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredThirtyNineEG_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredThirtyNineEG_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredThirtyNineEG_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredThirtyNineEG_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredThirtyNineEG_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredThirtyNineEG_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredThirtyNineEG_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredThirtyNineEG_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredThirtyNineEG_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredThirtyNineEG_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredThirtyNineEG_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredThirtyNineEG_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredThirtyNineEG_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredThirtyNineEG_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredThirtyNineEG_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredThirtyNineEG_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredThirtyNineEG_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredThirtyNineEG_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredThirtyNineEG_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredThirtyNineEG_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2531 : Nat.Prime 2531 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3037 : Nat.Prime 3037 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3079 : Nat.Prime 3079 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3187 : Nat.Prime 3187 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3343 : Nat.Prime 3343 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3571 : Nat.Prime 3571 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3607 : Nat.Prime 3607 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3761 : Nat.Prime 3761 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3863 : Nat.Prime 3863 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4243 : Nat.Prime 4243 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4297 : Nat.Prime 4297 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5051 : Nat.Prime 5051 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5113 : Nat.Prime 5113 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5323 : Nat.Prime 5323 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5501 : Nat.Prime 5501 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5783 : Nat.Prime 5783 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5851 : Nat.Prime 5851 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5981 : Nat.Prime 5981 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6073 : Nat.Prime 6073 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6173 : Nat.Prime 6173 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6317 : Nat.Prime 6317 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6337 : Nat.Prime 6337 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6343 : Nat.Prime 6343 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6379 : Nat.Prime 6379 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6491 : Nat.Prime 6491 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6577 : Nat.Prime 6577 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6691 : Nat.Prime 6691 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6719 : Nat.Prime 6719 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6803 : Nat.Prime 6803 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6947 : Nat.Prime 6947 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6949 : Nat.Prime 6949 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7207 : Nat.Prime 7207 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7219 : Nat.Prime 7219 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7411 : Nat.Prime 7411 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7547 : Nat.Prime 7547 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7901 : Nat.Prime 7901 := by norm_num

private theorem prime_oneHundredThirtyNineEG_8389 : Nat.Prime 8389 := by norm_num

private theorem prime_oneHundredThirtyNineEG_8527 : Nat.Prime 8527 := by norm_num

private theorem prime_oneHundredThirtyNineEG_8623 : Nat.Prime 8623 := by norm_num

private theorem prime_oneHundredThirtyNineEG_8737 : Nat.Prime 8737 := by norm_num

private theorem prime_oneHundredThirtyNineEG_8803 : Nat.Prime 8803 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9059 : Nat.Prime 9059 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9241 : Nat.Prime 9241 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9323 : Nat.Prime 9323 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9413 : Nat.Prime 9413 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9467 : Nat.Prime 9467 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9497 : Nat.Prime 9497 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10111 : Nat.Prime 10111 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10163 : Nat.Prime 10163 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10433 : Nat.Prime 10433 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10559 : Nat.Prime 10559 := by norm_num

private theorem prime_oneHundredThirtyNineEG_12689 : Nat.Prime 12689 := by norm_num

private theorem prime_oneHundredThirtyNineEG_14293 : Nat.Prime 14293 := by norm_num

private theorem prime_oneHundredThirtyNineEG_14639 : Nat.Prime 14639 := by norm_num

private theorem prime_oneHundredThirtyNineEG_15107 : Nat.Prime 15107 := by norm_num

private theorem prime_oneHundredThirtyNineEG_15511 : Nat.Prime 15511 := by norm_num

private theorem prime_oneHundredThirtyNineEG_15629 : Nat.Prime 15629 := by norm_num

private theorem prime_oneHundredThirtyNineEG_16619 : Nat.Prime 16619 := by norm_num

private theorem prime_oneHundredThirtyNineEG_16703 : Nat.Prime 16703 := by norm_num

private theorem prime_oneHundredThirtyNineEG_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtyNineEG_18217 : Nat.Prime 18217 := by norm_num

private theorem prime_oneHundredThirtyNineEG_18803 : Nat.Prime 18803 := by norm_num

private theorem prime_oneHundredThirtyNineEG_18973 : Nat.Prime 18973 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20011 : Nat.Prime 20011 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20089 : Nat.Prime 20089 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20147 : Nat.Prime 20147 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20149 : Nat.Prime 20149 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20219 : Nat.Prime 20219 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtyNineEG_21491 : Nat.Prime 21491 := by norm_num

private theorem prime_oneHundredThirtyNineEG_22067 : Nat.Prime 22067 := by norm_num

private theorem prime_oneHundredThirtyNineEG_22133 : Nat.Prime 22133 := by norm_num

private theorem prime_oneHundredThirtyNineEG_22193 : Nat.Prime 22193 := by norm_num

private theorem prime_oneHundredThirtyNineEG_22861 : Nat.Prime 22861 := by norm_num

private theorem prime_oneHundredThirtyNineEG_23081 : Nat.Prime 23081 := by norm_num

private theorem prime_oneHundredThirtyNineEG_24517 : Nat.Prime 24517 := by norm_num

private theorem prime_oneHundredThirtyNineEG_24623 : Nat.Prime 24623 := by norm_num

private theorem prime_oneHundredThirtyNineEG_24859 : Nat.Prime 24859 := by norm_num

private theorem prime_oneHundredThirtyNineEG_26141 : Nat.Prime 26141 := by norm_num

private theorem prime_oneHundredThirtyNineEG_26987 : Nat.Prime 26987 := by norm_num

private theorem prime_oneHundredThirtyNineEG_27481 : Nat.Prime 27481 := by norm_num

private theorem prime_oneHundredThirtyNineEG_27953 : Nat.Prime 27953 := by norm_num

private theorem prime_oneHundredThirtyNineEG_28607 : Nat.Prime 28607 := by norm_num

private theorem prime_oneHundredThirtyNineEG_29077 : Nat.Prime 29077 := by norm_num

private theorem prime_oneHundredThirtyNineEG_29297 : Nat.Prime 29297 := by norm_num

private theorem prime_oneHundredThirtyNineEG_31489 : Nat.Prime 31489 := by norm_num

private theorem prime_oneHundredThirtyNineEG_32479 : Nat.Prime 32479 := by norm_num

private theorem prime_oneHundredThirtyNineEG_32693 : Nat.Prime 32693 := by norm_num

private theorem prime_oneHundredThirtyNineEG_33893 : Nat.Prime 33893 := by norm_num

private theorem prime_oneHundredThirtyNineEG_34039 : Nat.Prime 34039 := by norm_num

private theorem prime_oneHundredThirtyNineEG_34981 : Nat.Prime 34981 := by norm_num

private theorem prime_oneHundredThirtyNineEG_38329 : Nat.Prime 38329 := by norm_num

private theorem prime_oneHundredThirtyNineEG_40849 : Nat.Prime 40849 := by norm_num

private theorem prime_oneHundredThirtyNineEG_41039 : Nat.Prime 41039 := by norm_num

private theorem prime_oneHundredThirtyNineEG_41903 : Nat.Prime 41903 := by norm_num

private theorem prime_oneHundredThirtyNineEG_42299 : Nat.Prime 42299 := by norm_num

private theorem prime_oneHundredThirtyNineEG_42349 : Nat.Prime 42349 := by norm_num

private theorem prime_oneHundredThirtyNineEG_42709 : Nat.Prime 42709 := by norm_num

private theorem prime_oneHundredThirtyNineEG_44017 : Nat.Prime 44017 := by norm_num

private theorem prime_oneHundredThirtyNineEG_44351 : Nat.Prime 44351 := by norm_num

private theorem prime_oneHundredThirtyNineEG_45707 : Nat.Prime 45707 := by norm_num

private theorem prime_oneHundredThirtyNineEG_45823 : Nat.Prime 45823 := by norm_num

private theorem prime_oneHundredThirtyNineEG_51199 : Nat.Prime 51199 := by norm_num

private theorem prime_oneHundredThirtyNineEG_56299 : Nat.Prime 56299 := by norm_num

private theorem prime_oneHundredThirtyNineEG_56611 : Nat.Prime 56611 := by norm_num

private theorem prime_oneHundredThirtyNineEG_57973 : Nat.Prime 57973 := by norm_num

private theorem prime_oneHundredThirtyNineEG_58337 : Nat.Prime 58337 := by norm_num

private theorem prime_oneHundredThirtyNineEG_58451 : Nat.Prime 58451 := by norm_num

private theorem prime_oneHundredThirtyNineEG_62653 : Nat.Prime 62653 := by norm_num

private theorem prime_oneHundredThirtyNineEG_62869 : Nat.Prime 62869 := by norm_num

private theorem prime_oneHundredThirtyNineEG_64513 : Nat.Prime 64513 := by norm_num

private theorem prime_oneHundredThirtyNineEG_67967 : Nat.Prime 67967 := by norm_num

private theorem prime_oneHundredThirtyNineEG_68171 : Nat.Prime 68171 := by norm_num

private theorem prime_oneHundredThirtyNineEG_69109 : Nat.Prime 69109 := by norm_num

private theorem prime_oneHundredThirtyNineEG_71389 : Nat.Prime 71389 := by norm_num

private theorem prime_oneHundredThirtyNineEG_72977 : Nat.Prime 72977 := by norm_num

private theorem prime_oneHundredThirtyNineEG_78259 : Nat.Prime 78259 := by norm_num

private theorem prime_oneHundredThirtyNineEG_78781 : Nat.Prime 78781 := by norm_num

private theorem prime_oneHundredThirtyNineEG_79939 : Nat.Prime 79939 := by norm_num

private theorem prime_oneHundredThirtyNineEG_81637 : Nat.Prime 81637 := by norm_num

private theorem prime_oneHundredThirtyNineEG_85691 : Nat.Prime 85691 := by norm_num

private theorem prime_oneHundredThirtyNineEG_87877 : Nat.Prime 87877 := by norm_num

private theorem prime_oneHundredThirtyNineEG_88997 : Nat.Prime 88997 := by norm_num

private theorem prime_oneHundredThirtyNineEG_92789 : Nat.Prime 92789 := by norm_num

private theorem prime_oneHundredThirtyNineEG_95279 : Nat.Prime 95279 := by norm_num

private theorem prime_oneHundredThirtyNineEG_96059 : Nat.Prime 96059 := by norm_num

private theorem prime_oneHundredThirtyNineEG_99623 : Nat.Prime 99623 := by norm_num

private theorem prime_oneHundredThirtyNineEG_110419 : Nat.Prime 110419 := by norm_num

private theorem prime_oneHundredThirtyNineEG_110581 : Nat.Prime 110581 := by norm_num

private theorem prime_oneHundredThirtyNineEG_113809 : Nat.Prime 113809 := by norm_num

private theorem prime_oneHundredThirtyNineEG_119533 : Nat.Prime 119533 := by norm_num

private theorem prime_oneHundredThirtyNineEG_119831 : Nat.Prime 119831 := by norm_num

private theorem prime_oneHundredThirtyNineEG_121867 : Nat.Prime 121867 := by norm_num

private theorem prime_oneHundredThirtyNineEG_123001 : Nat.Prime 123001 := by norm_num

private theorem prime_oneHundredThirtyNineEG_129347 : Nat.Prime 129347 := by norm_num

private theorem prime_oneHundredThirtyNineEG_133447 : Nat.Prime 133447 := by norm_num

private theorem prime_oneHundredThirtyNineEG_134033 : Nat.Prime 134033 := by norm_num

private theorem prime_oneHundredThirtyNineEG_134909 : Nat.Prime 134909 := by norm_num

private theorem prime_oneHundredThirtyNineEG_140419 : Nat.Prime 140419 := by norm_num

private theorem prime_oneHundredThirtyNineEG_148549 : Nat.Prime 148549 := by norm_num

private theorem prime_oneHundredThirtyNineEG_157411 : Nat.Prime 157411 := by norm_num

private theorem prime_oneHundredThirtyNineEG_157679 : Nat.Prime 157679 := by norm_num

private theorem prime_oneHundredThirtyNineEG_166739 : Nat.Prime 166739 := by norm_num

private theorem prime_oneHundredThirtyNineEG_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtyNineEG_177883 : Nat.Prime 177883 := by norm_num

private theorem prime_oneHundredThirtyNineEG_193847 : Nat.Prime 193847 := by norm_num

private theorem prime_oneHundredThirtyNineEG_198193 : Nat.Prime 198193 := by norm_num

private theorem prime_oneHundredThirtyNineEG_204521 : Nat.Prime 204521 := by norm_num

private theorem prime_oneHundredThirtyNineEG_210173 : Nat.Prime 210173 := by norm_num

private theorem prime_oneHundredThirtyNineEG_211747 : Nat.Prime 211747 := by norm_num

private theorem prime_oneHundredThirtyNineEG_238151 : Nat.Prime 238151 := by norm_num

private theorem prime_oneHundredThirtyNineEG_257297 : Nat.Prime 257297 := by norm_num

private theorem prime_oneHundredThirtyNineEG_259991 : Nat.Prime 259991 := by norm_num

private theorem prime_oneHundredThirtyNineEG_264071 : Nat.Prime 264071 := by norm_num

private theorem prime_oneHundredThirtyNineEG_266863 : Nat.Prime 266863 := by norm_num

private theorem prime_oneHundredThirtyNineEG_290351 : Nat.Prime 290351 := by norm_num

private theorem prime_oneHundredThirtyNineEG_294523 : Nat.Prime 294523 := by norm_num

private theorem prime_oneHundredThirtyNineEG_299723 : Nat.Prime 299723 := by norm_num

private theorem prime_oneHundredThirtyNineEG_319937 : Nat.Prime 319937 := by norm_num

private theorem prime_oneHundredThirtyNineEG_320041 : Nat.Prime 320041 := by norm_num

private theorem prime_oneHundredThirtyNineEG_324529 : Nat.Prime 324529 := by norm_num

private theorem prime_oneHundredThirtyNineEG_331451 : Nat.Prime 331451 := by norm_num

private theorem prime_oneHundredThirtyNineEG_363017 : Nat.Prime 363017 := by norm_num

private theorem prime_oneHundredThirtyNineEG_368507 : Nat.Prime 368507 := by norm_num

private theorem prime_oneHundredThirtyNineEG_381103 : Nat.Prime 381103 := by norm_num

private theorem prime_oneHundredThirtyNineEG_393209 : Nat.Prime 393209 := by norm_num

private theorem prime_oneHundredThirtyNineEG_401069 : Nat.Prime 401069 := by norm_num

private theorem prime_oneHundredThirtyNineEG_418813 : Nat.Prime 418813 := by norm_num

private theorem prime_oneHundredThirtyNineEG_439697 : Nat.Prime 439697 := by norm_num

private theorem prime_oneHundredThirtyNineEG_458039 : Nat.Prime 458039 := by norm_num

private theorem prime_oneHundredThirtyNineEG_485209 : Nat.Prime 485209 := by norm_num

private theorem prime_oneHundredThirtyNineEG_488513 : Nat.Prime 488513 := by norm_num

private theorem prime_oneHundredThirtyNineEG_528191 : Nat.Prime 528191 := by norm_num

private theorem prime_oneHundredThirtyNineEG_616321 : Nat.Prime 616321 := by norm_num

private theorem prime_oneHundredThirtyNineEG_616741 : Nat.Prime 616741 := by norm_num

private theorem prime_oneHundredThirtyNineEG_626783 : Nat.Prime 626783 := by norm_num

private theorem prime_oneHundredThirtyNineEG_666427 : Nat.Prime 666427 := by norm_num

private theorem prime_oneHundredThirtyNineEG_712007 : Nat.Prime 712007 := by norm_num

private theorem prime_oneHundredThirtyNineEG_747239 : Nat.Prime 747239 := by norm_num

private theorem prime_oneHundredThirtyNineEG_751061 : Nat.Prime 751061 := by norm_num

private theorem prime_oneHundredThirtyNineEG_775811 : Nat.Prime 775811 := by norm_num

private theorem prime_oneHundredThirtyNineEG_781321 : Nat.Prime 781321 := by norm_num

private theorem prime_oneHundredThirtyNineEG_798641 : Nat.Prime 798641 := by norm_num

private theorem prime_oneHundredThirtyNineEG_805741 : Nat.Prime 805741 := by norm_num

private theorem prime_oneHundredThirtyNineEG_837979 : Nat.Prime 837979 := by norm_num

private theorem prime_oneHundredThirtyNineEG_845653 : Nat.Prime 845653 := by norm_num

private theorem prime_oneHundredThirtyNineEG_864427 : Nat.Prime 864427 := by norm_num

private theorem prime_oneHundredThirtyNineEG_865661 : Nat.Prime 865661 := by norm_num

private theorem prime_oneHundredThirtyNineEG_873113 : Nat.Prime 873113 := by norm_num

private theorem prime_oneHundredThirtyNineEG_894301 : Nat.Prime 894301 := by norm_num

private theorem prime_oneHundredThirtyNineEG_900583 : Nat.Prime 900583 := by norm_num

private theorem prime_oneHundredThirtyNineEG_909529 : Nat.Prime 909529 := by norm_num

private theorem prime_oneHundredThirtyNineEG_909863 : Nat.Prime 909863 := by norm_num

private theorem prime_oneHundredThirtyNineEG_972199 : Nat.Prime 972199 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1087753 : Nat.Prime 1087753 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1093657 : Nat.Prime 1093657 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1118137 : Nat.Prime 1118137 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1131343 : Nat.Prime 1131343 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1174727 : Nat.Prime 1174727 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1203619 : Nat.Prime 1203619 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1273159 : Nat.Prime 1273159 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1274921 : Nat.Prime 1274921 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1332491 : Nat.Prime 1332491 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1382237 : Nat.Prime 1382237 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1390069 : Nat.Prime 1390069 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1433357 : Nat.Prime 1433357 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1467107 : Nat.Prime 1467107 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1491701 : Nat.Prime 1491701 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1635761 : Nat.Prime 1635761 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1708037 : Nat.Prime 1708037 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1776739 : Nat.Prime 1776739 := by norm_num

private theorem prime_oneHundredThirtyNineEG_1948799 : Nat.Prime 1948799 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2052317 : Nat.Prime 2052317 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2130703 : Nat.Prime 2130703 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2226701 : Nat.Prime 2226701 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2232437 : Nat.Prime 2232437 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2235239 : Nat.Prime 2235239 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2254927 : Nat.Prime 2254927 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2491327 : Nat.Prime 2491327 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2624099 : Nat.Prime 2624099 := by norm_num

private theorem prime_oneHundredThirtyNineEG_2990401 : Nat.Prime 2990401 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3022267 : Nat.Prime 3022267 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3115751 : Nat.Prime 3115751 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3162517 : Nat.Prime 3162517 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3436757 : Nat.Prime 3436757 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3483847 : Nat.Prime 3483847 := by norm_num

private theorem prime_oneHundredThirtyNineEG_3807449 : Nat.Prime 3807449 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4285381 : Nat.Prime 4285381 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4334497 : Nat.Prime 4334497 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4398091 : Nat.Prime 4398091 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4691383 : Nat.Prime 4691383 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4897219 : Nat.Prime 4897219 := by norm_num

private theorem prime_oneHundredThirtyNineEG_4957063 : Nat.Prime 4957063 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5070277 : Nat.Prime 5070277 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5244011 : Nat.Prime 5244011 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5269259 : Nat.Prime 5269259 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5464981 : Nat.Prime 5464981 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5599427 : Nat.Prime 5599427 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5670451 : Nat.Prime 5670451 := by norm_num

private theorem prime_oneHundredThirtyNineEG_5746457 : Nat.Prime 5746457 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6109427 : Nat.Prime 6109427 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6155519 : Nat.Prime 6155519 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6554413 : Nat.Prime 6554413 := by norm_num

private theorem prime_oneHundredThirtyNineEG_6986431 : Nat.Prime 6986431 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7029661 : Nat.Prime 7029661 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7738037 : Nat.Prime 7738037 := by norm_num

private theorem prime_oneHundredThirtyNineEG_7939637 : Nat.Prime 7939637 := by norm_num

private theorem prime_oneHundredThirtyNineEG_8559599 : Nat.Prime 8559599 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9049553 : Nat.Prime 9049553 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9241963 : Nat.Prime 9241963 := by norm_num

private theorem prime_oneHundredThirtyNineEG_9946109 : Nat.Prime 9946109 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10648459 : Nat.Prime 10648459 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10739543 : Nat.Prime 10739543 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10796917 : Nat.Prime 10796917 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtyNineEG_10908731 : Nat.Prime 10908731 := by norm_num

private theorem prime_oneHundredThirtyNineEG_11193331 : Nat.Prime 11193331 := by norm_num

private theorem prime_oneHundredThirtyNineEG_11364973 : Nat.Prime 11364973 := by norm_num

private theorem prime_oneHundredThirtyNineEG_14187493 : Nat.Prime 14187493 := by norm_num

private theorem prime_oneHundredThirtyNineEG_14592733 : Nat.Prime 14592733 := by norm_num

private theorem prime_oneHundredThirtyNineEG_14906933 : Nat.Prime 14906933 := by norm_num

private theorem prime_oneHundredThirtyNineEG_14992261 : Nat.Prime 14992261 := by norm_num

private theorem prime_oneHundredThirtyNineEG_15053873 : Nat.Prime 15053873 := by norm_num

private theorem prime_oneHundredThirtyNineEG_15481901 : Nat.Prime 15481901 := by norm_num

private theorem prime_oneHundredThirtyNineEG_15767497 : Nat.Prime 15767497 := by norm_num

private theorem prime_oneHundredThirtyNineEG_16836271 : Nat.Prime 16836271 := by norm_num

private theorem prime_oneHundredThirtyNineEG_18197009 : Nat.Prime 18197009 := by norm_num

private theorem prime_oneHundredThirtyNineEG_19810801 : Nat.Prime 19810801 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20265871 : Nat.Prime 20265871 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20747087 : Nat.Prime 20747087 := by norm_num

private theorem prime_oneHundredThirtyNineEG_20773331 : Nat.Prime 20773331 := by norm_num

private theorem prime_oneHundredThirtyNineEG_23882101 : Nat.Prime 23882101 := by norm_num

private theorem prime_oneHundredThirtyNineEG_25437397 : Nat.Prime 25437397 := by norm_num

private theorem prime_oneHundredThirtyNineEG_26673949 : Nat.Prime 26673949 := by norm_num

private theorem prime_oneHundredThirtyNineEG_28200839 : Nat.Prime 28200839 := by norm_num

private theorem prime_oneHundredThirtyNineEG_28636291 : Nat.Prime 28636291 := by norm_num

private theorem prime_oneHundredThirtyNineEG_30267833 : Nat.Prime 30267833 := by
  apply lucas_primality 30267833 (3 : ZMod 30267833)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (89, 1), (6073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (89, 1), (6073, 1)] : List FactorBlock).map factorBlockValue).prod) = 30267833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_89
      · exact prime_oneHundredThirtyNineEG_6073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30267833) ^ 15133916 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30267833) ^ 4323976 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30267833) ^ 340088 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30267833) ^ 4984 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_35729411 : Nat.Prime 35729411 := by
  apply lucas_primality 35729411 (2 : ZMod 35729411)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (210173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (210173, 1)] : List FactorBlock).map factorBlockValue).prod) = 35729411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_210173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35729411) ^ 17864705 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35729411) ^ 7145882 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35729411) ^ 2101730 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35729411) ^ 170 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_40183867 : Nat.Prime 40183867 := by
  apply lucas_primality 40183867 (5 : ZMod 40183867)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2232437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2232437, 1)] : List FactorBlock).map factorBlockValue).prod) = 40183867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_2232437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 40183867) ^ 20091933 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 40183867) ^ 13394622 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 40183867) ^ 18 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_49202689 : Nat.Prime 49202689 := by
  apply lucas_primality 49202689 (17 : ZMod 49202689)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (103, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (103, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) = 49202689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_103
      · exact prime_oneHundredThirtyNineEG_311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 49202689) ^ 24601344 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 49202689) ^ 16400896 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 49202689) ^ 477696 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 49202689) ^ 158208 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_49303171 : Nat.Prime 49303171 := by
  apply lucas_primality 49303171 (2 : ZMod 49303171)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (78259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (78259, 1)] : List FactorBlock).map factorBlockValue).prod) = 49303171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_78259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49303171) ^ 24651585 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49303171) ^ 16434390 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49303171) ^ 9860634 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49303171) ^ 7043310 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49303171) ^ 630 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_50952329 : Nat.Prime 50952329 := by
  apply lucas_primality 50952329 (6 : ZMod 50952329)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (909863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (909863, 1)] : List FactorBlock).map factorBlockValue).prod) = 50952329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_909863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 50952329) ^ 25476164 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 50952329) ^ 7278904 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 50952329) ^ 56 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_55629713 : Nat.Prime 55629713 := by
  apply lucas_primality 55629713 (3 : ZMod 55629713)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (204521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (204521, 1)] : List FactorBlock).map factorBlockValue).prod) = 55629713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_204521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55629713) ^ 27814856 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55629713) ^ 3272336 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55629713) ^ 272 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_61060123 : Nat.Prime 61060123 := by
  apply lucas_primality 61060123 (2 : ZMod 61060123)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (179, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (179, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) = 61060123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_179
      · exact prime_oneHundredThirtyNineEG_6317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61060123) ^ 30530061 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61060123) ^ 20353374 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61060123) ^ 341118 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 61060123) ^ 9666 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_64256743 : Nat.Prime 64256743 := by
  apply lucas_primality 64256743 (5 : ZMod 64256743)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (324529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (324529, 1)] : List FactorBlock).map factorBlockValue).prod) = 64256743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_324529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64256743) ^ 32128371 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 64256743) ^ 21418914 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 64256743) ^ 5841522 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 64256743) ^ 198 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_65353439 : Nat.Prime 65353439 := by
  apply lucas_primality 65353439 (7 : ZMod 65353439)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (257297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (257297, 1)] : List FactorBlock).map factorBlockValue).prod) = 65353439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_127
      · exact prime_oneHundredThirtyNineEG_257297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 65353439) ^ 32676719 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 65353439) ^ 514594 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 65353439) ^ 254 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_70999129 : Nat.Prime 70999129 := by
  apply lucas_primality 70999129 (7 : ZMod 70999129)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (409, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (409, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) = 70999129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_409
      · exact prime_oneHundredThirtyNineEG_2411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 70999129) ^ 35499564 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 70999129) ^ 23666376 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 70999129) ^ 173592 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 70999129) ^ 29448 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_72101857 : Nat.Prime 72101857 := by
  apply lucas_primality 72101857 (17 : ZMod 72101857)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (751061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (751061, 1)] : List FactorBlock).map factorBlockValue).prod) = 72101857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_751061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 72101857) ^ 36050928 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 72101857) ^ 24033952 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 72101857) ^ 96 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_73044163 : Nat.Prime 73044163 := by
  apply lucas_primality 73044163 (2 : ZMod 73044163)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (617, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (617, 1), (6577, 1)] : List FactorBlock).map factorBlockValue).prod) = 73044163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_617
      · exact prime_oneHundredThirtyNineEG_6577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73044163) ^ 36522081 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73044163) ^ 24348054 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73044163) ^ 118386 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73044163) ^ 11106 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_76613371 : Nat.Prime 76613371 := by
  apply lucas_primality 76613371 (7 : ZMod 76613371)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1009, 1), (2531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1009, 1), (2531, 1)] : List FactorBlock).map factorBlockValue).prod) = 76613371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_1009
      · exact prime_oneHundredThirtyNineEG_2531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 76613371) ^ 38306685 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76613371) ^ 25537790 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76613371) ^ 15322674 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76613371) ^ 75930 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 76613371) ^ 30270 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_78346927 : Nat.Prime 78346927 := by
  apply lucas_primality 78346927 (3 : ZMod 78346927)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (59, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (59, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 78346927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_59
      · exact prime_oneHundredThirtyNineEG_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78346927) ^ 39173463 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78346927) ^ 26115642 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78346927) ^ 11192418 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78346927) ^ 1327914 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78346927) ^ 66906 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_78775481 : Nat.Prime 78775481 := by
  apply lucas_primality 78775481 (6 : ZMod 78775481)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (353, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (353, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 78775481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_353
      · exact prime_oneHundredThirtyNineEG_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 78775481) ^ 39387740 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 78775481) ^ 15755096 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 78775481) ^ 11253640 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 78775481) ^ 223160 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 78775481) ^ 98840 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_79313009 : Nat.Prime 79313009 := by
  apply lucas_primality 79313009 (3 : ZMod 79313009)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4957063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4957063, 1)] : List FactorBlock).map factorBlockValue).prod) = 79313009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_4957063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 79313009) ^ 39656504 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 79313009) ^ 16 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_80192999 : Nat.Prime 80192999 := by
  apply lucas_primality 80192999 (23 : ZMod 80192999)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (701, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (701, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 80192999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_701
      · exact prime_oneHundredThirtyNineEG_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 80192999) ^ 40096499 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (23 : ZMod 80192999) ^ 1706234 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (23 : ZMod 80192999) ^ 114398 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (23 : ZMod 80192999) ^ 65894 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_89065807 : Nat.Prime 89065807 := by
  apply lucas_primality 89065807 (3 : ZMod 89065807)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (83, 1), (9413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (83, 1), (9413, 1)] : List FactorBlock).map factorBlockValue).prod) = 89065807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_83
      · exact prime_oneHundredThirtyNineEG_9413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 89065807) ^ 44532903 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 89065807) ^ 29688602 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 89065807) ^ 4687674 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 89065807) ^ 1073082 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 89065807) ^ 9462 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_92377367 : Nat.Prime 92377367 := by
  apply lucas_primality 92377367 (5 : ZMod 92377367)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (647, 1), (71389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (647, 1), (71389, 1)] : List FactorBlock).map factorBlockValue).prod) = 92377367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_647
      · exact prime_oneHundredThirtyNineEG_71389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 92377367) ^ 46188683 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 92377367) ^ 142778 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 92377367) ^ 1294 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_110573363 : Nat.Prime 110573363 := by
  apply lucas_primality 110573363 (2 : ZMod 110573363)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (811, 1), (68171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (811, 1), (68171, 1)] : List FactorBlock).map factorBlockValue).prod) = 110573363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_811
      · exact prime_oneHundredThirtyNineEG_68171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 110573363) ^ 55286681 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110573363) ^ 136342 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110573363) ^ 1622 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_113771641 : Nat.Prime 113771641 := by
  apply lucas_primality 113771641 (31 : ZMod 113771641)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (29, 1), (32693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (29, 1), (32693, 1)] : List FactorBlock).map factorBlockValue).prod) = 113771641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_32693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 113771641) ^ 56885820 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (31 : ZMod 113771641) ^ 37923880 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (31 : ZMod 113771641) ^ 22754328 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (31 : ZMod 113771641) ^ 3923160 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (31 : ZMod 113771641) ^ 3480 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_122060303 : Nat.Prime 122060303 := by
  apply lucas_primality 122060303 (5 : ZMod 122060303)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (809, 1), (829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (809, 1), (829, 1)] : List FactorBlock).map factorBlockValue).prod) = 122060303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_809
      · exact prime_oneHundredThirtyNineEG_829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 122060303) ^ 61030151 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 122060303) ^ 17437186 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 122060303) ^ 9389254 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 122060303) ^ 150878 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 122060303) ^ 147238 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_124326077 : Nat.Prime 124326077 := by
  apply lucas_primality 124326077 (2 : ZMod 124326077)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1231, 1), (3607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1231, 1), (3607, 1)] : List FactorBlock).map factorBlockValue).prod) = 124326077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_1231
      · exact prime_oneHundredThirtyNineEG_3607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 124326077) ^ 62163038 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 124326077) ^ 17760868 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 124326077) ^ 100996 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 124326077) ^ 34468 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_126158183 : Nat.Prime 126158183 := by
  apply lucas_primality 126158183 (5 : ZMod 126158183)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (293, 1), (461, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (293, 1), (461, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 126158183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_293
      · exact prime_oneHundredThirtyNineEG_461
      · exact prime_oneHundredThirtyNineEG_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 126158183) ^ 63079091 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 126158183) ^ 430574 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 126158183) ^ 273662 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 126158183) ^ 270146 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_130706879 : Nat.Prime 130706879 := by
  apply lucas_primality 130706879 (7 : ZMod 130706879)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (65353439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (65353439, 1)] : List FactorBlock).map factorBlockValue).prod) = 130706879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_65353439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 130706879) ^ 65353439 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 130706879) ^ 2 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_131814101 : Nat.Prime 131814101 := by
  apply lucas_primality 131814101 (2 : ZMod 131814101)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (119831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (119831, 1)] : List FactorBlock).map factorBlockValue).prod) = 131814101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_119831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 131814101) ^ 65907050 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 131814101) ^ 26362820 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 131814101) ^ 11983100 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 131814101) ^ 1100 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_131911513 : Nat.Prime 131911513 := by
  apply lucas_primality 131911513 (5 : ZMod 131911513)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (148549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (148549, 1)] : List FactorBlock).map factorBlockValue).prod) = 131911513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_148549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 131911513) ^ 65955756 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 131911513) ^ 43970504 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 131911513) ^ 3565176 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 131911513) ^ 888 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_144531031 : Nat.Prime 144531031 := by
  apply lucas_primality 144531031 (3 : ZMod 144531031)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (311, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (311, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod) = 144531031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_311
      · exact prime_oneHundredThirtyNineEG_2213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 144531031) ^ 72265515 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144531031) ^ 48177010 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144531031) ^ 28906206 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144531031) ^ 20647290 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144531031) ^ 464730 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144531031) ^ 65310 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_157741301 : Nat.Prime 157741301 := by
  apply lucas_primality 157741301 (10 : ZMod 157741301)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (17, 1), (92789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (17, 1), (92789, 1)] : List FactorBlock).map factorBlockValue).prod) = 157741301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_92789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 157741301) ^ 78870650 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 157741301) ^ 31548260 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 157741301) ^ 9278900 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 157741301) ^ 1700 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_160385999 : Nat.Prime 160385999 := by
  apply lucas_primality 160385999 (7 : ZMod 160385999)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80192999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80192999, 1)] : List FactorBlock).map factorBlockValue).prod) = 160385999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_80192999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 160385999) ^ 80192999 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 160385999) ^ 2 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_160413287 : Nat.Prime 160413287 := by
  apply lucas_primality 160413287 (5 : ZMod 160413287)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (119533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (119533, 1)] : List FactorBlock).map factorBlockValue).prod) = 160413287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_61
      · exact prime_oneHundredThirtyNineEG_119533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 160413287) ^ 80206643 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 160413287) ^ 14583026 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 160413287) ^ 2629726 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 160413287) ^ 1342 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_164636113 : Nat.Prime 164636113 := by
  apply lucas_primality 164636113 (5 : ZMod 164636113)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (47, 1), (72977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (47, 1), (72977, 1)] : List FactorBlock).map factorBlockValue).prod) = 164636113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_72977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 164636113) ^ 82318056 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 164636113) ^ 54878704 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 164636113) ^ 3502896 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 164636113) ^ 2256 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_170534597 : Nat.Prime 170534597 := by
  apply lucas_primality 170534597 (2 : ZMod 170534597)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (739, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (739, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) = 170534597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_31
      · exact prime_oneHundredThirtyNineEG_739
      · exact prime_oneHundredThirtyNineEG_1861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 170534597) ^ 85267298 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 170534597) ^ 5501116 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 170534597) ^ 230764 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 170534597) ^ 91636 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_181336021 : Nat.Prime 181336021 := by
  apply lucas_primality 181336021 (2 : ZMod 181336021)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3022267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3022267, 1)] : List FactorBlock).map factorBlockValue).prod) = 181336021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_3022267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 181336021) ^ 90668010 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 181336021) ^ 60445340 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 181336021) ^ 36267204 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 181336021) ^ 60 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_187224509 : Nat.Prime 187224509 := by
  apply lucas_primality 187224509 (2 : ZMod 187224509)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (101, 1), (20149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (101, 1), (20149, 1)] : List FactorBlock).map factorBlockValue).prod) = 187224509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_101
      · exact prime_oneHundredThirtyNineEG_20149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 187224509) ^ 93612254 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 187224509) ^ 8140196 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 187224509) ^ 1853708 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 187224509) ^ 9292 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_188127739 : Nat.Prime 188127739 := by
  apply lucas_primality 188127739 (2 : ZMod 188127739)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3483847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3483847, 1)] : List FactorBlock).map factorBlockValue).prod) = 188127739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_3483847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 188127739) ^ 94063869 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 188127739) ^ 62709246 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 188127739) ^ 54 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_196632391 : Nat.Prime 196632391 := by
  apply lucas_primality 196632391 (7 : ZMod 196632391)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (6554413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (6554413, 1)] : List FactorBlock).map factorBlockValue).prod) = 196632391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_6554413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 196632391) ^ 98316195 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 196632391) ^ 65544130 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 196632391) ^ 39326478 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 196632391) ^ 30 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_209227819 : Nat.Prime 209227819 := by
  apply lucas_primality 209227819 (3 : ZMod 209227819)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (761, 1), (45823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (761, 1), (45823, 1)] : List FactorBlock).map factorBlockValue).prod) = 209227819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_761
      · exact prime_oneHundredThirtyNineEG_45823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 209227819) ^ 104613909 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 209227819) ^ 69742606 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 209227819) ^ 274938 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 209227819) ^ 4566 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_231065587 : Nat.Prime 231065587 := by
  apply lucas_primality 231065587 (2 : ZMod 231065587)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (73, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (73, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) = 231065587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_41
      · exact prime_oneHundredThirtyNineEG_73
      · exact prime_oneHundredThirtyNineEG_4289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 231065587) ^ 115532793 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 231065587) ^ 77021862 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 231065587) ^ 5635746 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 231065587) ^ 3165282 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 231065587) ^ 53874 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_243912283 : Nat.Prime 243912283 := by
  apply lucas_primality 243912283 (3 : ZMod 243912283)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (666427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (666427, 1)] : List FactorBlock).map factorBlockValue).prod) = 243912283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_61
      · exact prime_oneHundredThirtyNineEG_666427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 243912283) ^ 121956141 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 243912283) ^ 81304094 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 243912283) ^ 3998562 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 243912283) ^ 366 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_251483923 : Nat.Prime 251483923 := by
  apply lucas_primality 251483923 (2 : ZMod 251483923)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (691, 1), (20219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (691, 1), (20219, 1)] : List FactorBlock).map factorBlockValue).prod) = 251483923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_691
      · exact prime_oneHundredThirtyNineEG_20219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 251483923) ^ 125741961 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 251483923) ^ 83827974 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 251483923) ^ 363942 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 251483923) ^ 12438 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_260520487 : Nat.Prime 260520487 := by
  apply lucas_primality 260520487 (3 : ZMod 260520487)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (331451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (331451, 1)] : List FactorBlock).map factorBlockValue).prod) = 260520487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_131
      · exact prime_oneHundredThirtyNineEG_331451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 260520487) ^ 130260243 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 260520487) ^ 86840162 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 260520487) ^ 1988706 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 260520487) ^ 786 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_335965621 : Nat.Prime 335965621 := by
  apply lucas_primality 335965621 (6 : ZMod 335965621)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (5599427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (5599427, 1)] : List FactorBlock).map factorBlockValue).prod) = 335965621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_5599427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 335965621) ^ 167982810 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 335965621) ^ 111988540 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 335965621) ^ 67193124 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 335965621) ^ 60 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_347962513 : Nat.Prime 347962513 := by
  apply lucas_primality 347962513 (5 : ZMod 347962513)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (173, 1), (41903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (173, 1), (41903, 1)] : List FactorBlock).map factorBlockValue).prod) = 347962513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_173
      · exact prime_oneHundredThirtyNineEG_41903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 347962513) ^ 173981256 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 347962513) ^ 115987504 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 347962513) ^ 2011344 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 347962513) ^ 8304 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_394736227 : Nat.Prime 394736227 := by
  apply lucas_primality 394736227 (2 : ZMod 394736227)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (29, 1), (133447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (29, 1), (133447, 1)] : List FactorBlock).map factorBlockValue).prod) = 394736227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_133447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 394736227) ^ 197368113 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 394736227) ^ 131578742 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 394736227) ^ 23219778 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 394736227) ^ 13611594 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 394736227) ^ 2958 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_395481607 : Nat.Prime 395481607 := by
  apply lucas_primality 395481607 (3 : ZMod 395481607)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (5070277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (5070277, 1)] : List FactorBlock).map factorBlockValue).prod) = 395481607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_5070277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 395481607) ^ 197740803 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 395481607) ^ 131827202 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 395481607) ^ 30421662 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 395481607) ^ 78 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_506952847 : Nat.Prime 506952847 := by
  apply lucas_primality 506952847 (5 : ZMod 506952847)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (97, 1), (290351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (97, 1), (290351, 1)] : List FactorBlock).map factorBlockValue).prod) = 506952847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_97
      · exact prime_oneHundredThirtyNineEG_290351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 506952847) ^ 253476423 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 506952847) ^ 168984282 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 506952847) ^ 5226318 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 506952847) ^ 1746 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_529355549 : Nat.Prime 529355549 := by
  apply lucas_primality 529355549 (2 : ZMod 529355549)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (197, 1), (14293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (197, 1), (14293, 1)] : List FactorBlock).map factorBlockValue).prod) = 529355549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_197
      · exact prime_oneHundredThirtyNineEG_14293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 529355549) ^ 264677774 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 529355549) ^ 11262884 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 529355549) ^ 2687084 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 529355549) ^ 37036 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_611922887 : Nat.Prime 611922887 := by
  apply lucas_primality 611922887 (5 : ZMod 611922887)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (1948799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (1948799, 1)] : List FactorBlock).map factorBlockValue).prod) = 611922887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_157
      · exact prime_oneHundredThirtyNineEG_1948799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 611922887) ^ 305961443 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 611922887) ^ 3897598 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 611922887) ^ 314 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_614279041 : Nat.Prime 614279041 := by
  apply lucas_primality 614279041 (7 : ZMod 614279041)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (319937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (319937, 1)] : List FactorBlock).map factorBlockValue).prod) = 614279041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_319937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 614279041) ^ 307139520 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 614279041) ^ 204759680 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 614279041) ^ 122855808 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 614279041) ^ 1920 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_17203
      · exact prime_oneHundredThirtyNineEG_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_756949099 : Nat.Prime 756949099 := by
  apply lucas_primality 756949099 (3 : ZMod 756949099)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (126158183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (126158183, 1)] : List FactorBlock).map factorBlockValue).prod) = 756949099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_126158183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 756949099) ^ 378474549 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 756949099) ^ 252316366 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 756949099) ^ 6 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_821515507 : Nat.Prime 821515507 := by
  apply lucas_primality 821515507 (5 : ZMod 821515507)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3343, 1), (5851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3343, 1), (5851, 1)] : List FactorBlock).map factorBlockValue).prod) = 821515507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_3343
      · exact prime_oneHundredThirtyNineEG_5851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 821515507) ^ 410757753 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 821515507) ^ 273838502 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 821515507) ^ 117359358 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 821515507) ^ 245742 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 821515507) ^ 140406 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_895619239 : Nat.Prime 895619239 := by
  apply lucas_primality 895619239 (6 : ZMod 895619239)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (557, 1), (9241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (557, 1), (9241, 1)] : List FactorBlock).map factorBlockValue).prod) = 895619239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_557
      · exact prime_oneHundredThirtyNineEG_9241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 895619239) ^ 447809619 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 895619239) ^ 298539746 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 895619239) ^ 30883422 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 895619239) ^ 1607934 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 895619239) ^ 96918 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_912793213 : Nat.Prime 912793213 := by
  apply lucas_primality 912793213 (2 : ZMod 912793213)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (19, 1), (29, 1), (5113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (19, 1), (29, 1), (5113, 1)] : List FactorBlock).map factorBlockValue).prod) = 912793213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_5113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 912793213) ^ 456396606 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 912793213) ^ 304264404 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 912793213) ^ 48041748 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 912793213) ^ 31475628 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 912793213) ^ 178524 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_975317573 : Nat.Prime 975317573 := by
  apply lucas_primality 975317573 (2 : ZMod 975317573)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (5670451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (5670451, 1)] : List FactorBlock).map factorBlockValue).prod) = 975317573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_43
      · exact prime_oneHundredThirtyNineEG_5670451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 975317573) ^ 487658786 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 975317573) ^ 22681804 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 975317573) ^ 172 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_979648079 : Nat.Prime 979648079 := by
  apply lucas_primality 979648079 (7 : ZMod 979648079)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (9241963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (9241963, 1)] : List FactorBlock).map factorBlockValue).prod) = 979648079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_53
      · exact prime_oneHundredThirtyNineEG_9241963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 979648079) ^ 489824039 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 979648079) ^ 18483926 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 979648079) ^ 106 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1131291947 : Nat.Prime 1131291947 := by
  apply lucas_primality 1131291947 (2 : ZMod 1131291947)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (761, 1), (20089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (761, 1), (20089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1131291947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_761
      · exact prime_oneHundredThirtyNineEG_20089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1131291947) ^ 565645973 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1131291947) ^ 30575458 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1131291947) ^ 1486586 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1131291947) ^ 56314 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1259889307 : Nat.Prime 1259889307 := by
  apply lucas_primality 1259889307 (2 : ZMod 1259889307)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (67, 1), (491, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (67, 1), (491, 2)] : List FactorBlock).map factorBlockValue).prod) = 1259889307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_67
      · exact prime_oneHundredThirtyNineEG_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1259889307) ^ 629944653 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259889307) ^ 419963102 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259889307) ^ 96914562 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259889307) ^ 18804318 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259889307) ^ 2565966 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1263815893 : Nat.Prime 1263815893 := by
  apply lucas_primality 1263815893 (2 : ZMod 1263815893)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1621, 1), (7219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1621, 1), (7219, 1)] : List FactorBlock).map factorBlockValue).prod) = 1263815893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_1621
      · exact prime_oneHundredThirtyNineEG_7219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1263815893) ^ 631907946 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1263815893) ^ 421271964 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1263815893) ^ 779652 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1263815893) ^ 175068 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1291902361 : Nat.Prime 1291902361 := by
  apply lucas_primality 1291902361 (22 : ZMod 1291902361)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (37, 1), (197, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (37, 1), (197, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291902361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_197
      · exact prime_oneHundredThirtyNineEG_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 1291902361) ^ 645951180 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (22 : ZMod 1291902361) ^ 430634120 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (22 : ZMod 1291902361) ^ 258380472 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (22 : ZMod 1291902361) ^ 184557480 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (22 : ZMod 1291902361) ^ 34916280 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (22 : ZMod 1291902361) ^ 6557880 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (22 : ZMod 1291902361) ^ 6122760 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1325781293 : Nat.Prime 1325781293 := by
  apply lucas_primality 1325781293 (2 : ZMod 1325781293)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1229, 1), (24517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1229, 1), (24517, 1)] : List FactorBlock).map factorBlockValue).prod) = 1325781293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_1229
      · exact prime_oneHundredThirtyNineEG_24517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1325781293) ^ 662890646 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1325781293) ^ 120525572 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1325781293) ^ 1078748 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1325781293) ^ 54076 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1401367531 : Nat.Prime 1401367531 := by
  apply lucas_primality 1401367531 (2 : ZMod 1401367531)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (103, 1), (127, 1), (3571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (103, 1), (127, 1), (3571, 1)] : List FactorBlock).map factorBlockValue).prod) = 1401367531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_103
      · exact prime_oneHundredThirtyNineEG_127
      · exact prime_oneHundredThirtyNineEG_3571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1401367531) ^ 700683765 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1401367531) ^ 467122510 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1401367531) ^ 280273506 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1401367531) ^ 13605510 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1401367531) ^ 11034390 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1401367531) ^ 392430 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1568161117 : Nat.Prime 1568161117 := by
  apply lucas_primality 1568161117 (2 : ZMod 1568161117)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (113, 1), (397, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (113, 1), (397, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1568161117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_113
      · exact prime_oneHundredThirtyNineEG_397
      · exact prime_oneHundredThirtyNineEG_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1568161117) ^ 784080558 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1568161117) ^ 522720372 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1568161117) ^ 13877532 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1568161117) ^ 3950028 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1568161117) ^ 1614996 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1649915609 : Nat.Prime 1649915609 := by
  apply lucas_primality 1649915609 (3 : ZMod 1649915609)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (71, 1), (264071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (71, 1), (264071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1649915609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_71
      · exact prime_oneHundredThirtyNineEG_264071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1649915609) ^ 824957804 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1649915609) ^ 149992328 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1649915609) ^ 23238248 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1649915609) ^ 6248 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1663186003 : Nat.Prime 1663186003 := by
  apply lucas_primality 1663186003 (2 : ZMod 1663186003)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8803, 1), (31489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8803, 1), (31489, 1)] : List FactorBlock).map factorBlockValue).prod) = 1663186003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_8803
      · exact prime_oneHundredThirtyNineEG_31489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1663186003) ^ 831593001 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1663186003) ^ 554395334 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1663186003) ^ 188934 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1663186003) ^ 52818 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1807017109 : Nat.Prime 1807017109 := by
  apply lucas_primality 1807017109 (10 : ZMod 1807017109)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (41, 1), (16619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (41, 1), (16619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1807017109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_41
      · exact prime_oneHundredThirtyNineEG_16619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1807017109) ^ 903508554 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1807017109) ^ 602339036 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1807017109) ^ 139001316 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1807017109) ^ 106295124 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1807017109) ^ 44073588 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 1807017109) ^ 108732 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1886471557 : Nat.Prime 1886471557 := by
  apply lucas_primality 1886471557 (2 : ZMod 1886471557)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (997, 1), (157679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (997, 1), (157679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1886471557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_997
      · exact prime_oneHundredThirtyNineEG_157679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1886471557) ^ 943235778 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1886471557) ^ 628823852 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1886471557) ^ 1892148 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1886471557) ^ 11964 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1911454271 : Nat.Prime 1911454271 := by
  apply lucas_primality 1911454271 (11 : ZMod 1911454271)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (59, 1), (294523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (59, 1), (294523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1911454271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_59
      · exact prime_oneHundredThirtyNineEG_294523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1911454271) ^ 955727135 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1911454271) ^ 382290854 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1911454271) ^ 173768570 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1911454271) ^ 32397530 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1911454271) ^ 6490 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2001677443 : Nat.Prime 2001677443 := by
  apply lucas_primality 2001677443 (3 : ZMod 2001677443)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (151, 1), (96059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (151, 1), (96059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2001677443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_151
      · exact prime_oneHundredThirtyNineEG_96059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2001677443) ^ 1000838721 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2001677443) ^ 667225814 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2001677443) ^ 87029454 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2001677443) ^ 13256142 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2001677443) ^ 20838 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2027811389 : Nat.Prime 2027811389 := by
  apply lucas_primality 2027811389 (2 : ZMod 2027811389)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (506952847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (506952847, 1)] : List FactorBlock).map factorBlockValue).prod) = 2027811389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_506952847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2027811389) ^ 1013905694 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2027811389) ^ 4 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2347805101 : Nat.Prime 2347805101 := by
  apply lucas_primality 2347805101 (2 : ZMod 2347805101)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (47, 1), (269, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (47, 1), (269, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 2347805101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_269
      · exact prime_oneHundredThirtyNineEG_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2347805101) ^ 1173902550 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2347805101) ^ 782601700 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2347805101) ^ 469561020 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2347805101) ^ 49953300 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2347805101) ^ 8727900 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2347805101) ^ 3792900 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2711395363 : Nat.Prime 2711395363 := by
  apply lucas_primality 2711395363 (2 : ZMod 2711395363)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (83, 1), (418813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (83, 1), (418813, 1)] : List FactorBlock).map factorBlockValue).prod) = 2711395363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_83
      · exact prime_oneHundredThirtyNineEG_418813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2711395363) ^ 1355697681 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2711395363) ^ 903798454 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2711395363) ^ 208568874 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2711395363) ^ 32667414 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2711395363) ^ 6474 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3082189333 : Nat.Prime 3082189333 := by
  apply lucas_primality 3082189333 (2 : ZMod 3082189333)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1213, 1), (211747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1213, 1), (211747, 1)] : List FactorBlock).map factorBlockValue).prod) = 3082189333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_1213
      · exact prime_oneHundredThirtyNineEG_211747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3082189333) ^ 1541094666 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3082189333) ^ 1027396444 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3082189333) ^ 2540964 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3082189333) ^ 14556 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3094866449 : Nat.Prime 3094866449 := by
  apply lucas_primality 3094866449 (3 : ZMod 3094866449)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (239, 1), (503, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (239, 1), (503, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) = 3094866449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_239
      · exact prime_oneHundredThirtyNineEG_503
      · exact prime_oneHundredThirtyNineEG_1609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3094866449) ^ 1547433224 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3094866449) ^ 12949232 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3094866449) ^ 6152816 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3094866449) ^ 1923472 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3240381041 : Nat.Prime 3240381041 := by
  apply lucas_primality 3240381041 (3 : ZMod 3240381041)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (3115751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (3115751, 1)] : List FactorBlock).map factorBlockValue).prod) = 3240381041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_3115751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3240381041) ^ 1620190520 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3240381041) ^ 648076208 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3240381041) ^ 249260080 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3240381041) ^ 1040 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3299831219 : Nat.Prime 3299831219 := by
  apply lucas_primality 3299831219 (2 : ZMod 3299831219)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1649915609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1649915609, 1)] : List FactorBlock).map factorBlockValue).prod) = 3299831219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_1649915609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3299831219) ^ 1649915609 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3299831219) ^ 2 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3384075941 : Nat.Prime 3384075941 := by
  apply lucas_primality 3384075941 (2 : ZMod 3384075941)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (31, 1), (41039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (31, 1), (41039, 1)] : List FactorBlock).map factorBlockValue).prod) = 3384075941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_31
      · exact prime_oneHundredThirtyNineEG_41039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3384075941) ^ 1692037970 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3384075941) ^ 676815188 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3384075941) ^ 483439420 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3384075941) ^ 178109260 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3384075941) ^ 109163740 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3384075941) ^ 82460 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3582476957 : Nat.Prime 3582476957 := by
  apply lucas_primality 3582476957 (2 : ZMod 3582476957)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (895619239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (895619239, 1)] : List FactorBlock).map factorBlockValue).prod) = 3582476957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_895619239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3582476957) ^ 1791238478 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3582476957) ^ 4 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3651172853 : Nat.Prime 3651172853 := by
  apply lucas_primality 3651172853 (2 : ZMod 3651172853)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (912793213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (912793213, 1)] : List FactorBlock).map factorBlockValue).prod) = 3651172853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_912793213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3651172853) ^ 1825586426 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3651172853) ^ 4 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4146797843 : Nat.Prime 4146797843 := by
  apply lucas_primality 4146797843 (2 : ZMod 4146797843)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (139, 1), (149, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (139, 1), (149, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 4146797843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_139
      · exact prime_oneHundredThirtyNineEG_149
      · exact prime_oneHundredThirtyNineEG_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4146797843) ^ 2073398921 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4146797843) ^ 376981622 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4146797843) ^ 218252518 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4146797843) ^ 29833078 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4146797843) ^ 27830858 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4146797843) ^ 8657198 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4889666627 : Nat.Prime 4889666627 := by
  apply lucas_primality 4889666627 (2 : ZMod 4889666627)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (293, 1), (22133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (293, 1), (22133, 1)] : List FactorBlock).map factorBlockValue).prod) = 4889666627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_293
      · exact prime_oneHundredThirtyNineEG_22133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4889666627) ^ 2444833313 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889666627) ^ 376128202 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889666627) ^ 168609194 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889666627) ^ 16688282 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889666627) ^ 220922 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4889992279 : Nat.Prime 4889992279 := by
  apply lucas_primality 4889992279 (6 : ZMod 4889992279)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1543, 1), (528191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1543, 1), (528191, 1)] : List FactorBlock).map factorBlockValue).prod) = 4889992279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_1543
      · exact prime_oneHundredThirtyNineEG_528191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4889992279) ^ 2444996139 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4889992279) ^ 1629997426 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4889992279) ^ 3169146 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 4889992279) ^ 9258 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_5211761117 : Nat.Prime 5211761117 := by
  apply lucas_primality 5211761117 (2 : ZMod 5211761117)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (9946109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (9946109, 1)] : List FactorBlock).map factorBlockValue).prod) = 5211761117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_131
      · exact prime_oneHundredThirtyNineEG_9946109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5211761117) ^ 2605880558 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5211761117) ^ 39784436 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5211761117) ^ 524 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_31
      · exact prime_oneHundredThirtyNineEG_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6395972059 : Nat.Prime 6395972059 := by
  apply lucas_primality 6395972059 (2 : ZMod 6395972059)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 2), (805741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 2), (805741, 1)] : List FactorBlock).map factorBlockValue).prod) = 6395972059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_805741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6395972059) ^ 3197986029 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6395972059) ^ 2131990686 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6395972059) ^ 913710294 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6395972059) ^ 7938 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6527276741 : Nat.Prime 6527276741 := by
  apply lucas_primality 6527276741 (2 : ZMod 6527276741)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (131, 1), (2491327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (131, 1), (2491327, 1)] : List FactorBlock).map factorBlockValue).prod) = 6527276741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_131
      · exact prime_oneHundredThirtyNineEG_2491327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6527276741) ^ 3263638370 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6527276741) ^ 1305455348 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6527276741) ^ 49826540 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6527276741) ^ 2620 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6855548507 : Nat.Prime 6855548507 := by
  apply lucas_primality 6855548507 (2 : ZMod 6855548507)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (110573363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (110573363, 1)] : List FactorBlock).map factorBlockValue).prod) = 6855548507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_31
      · exact prime_oneHundredThirtyNineEG_110573363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6855548507) ^ 3427774253 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6855548507) ^ 221146726 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6855548507) ^ 62 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_8300924609 : Nat.Prime 8300924609 := by
  apply lucas_primality 8300924609 (3 : ZMod 8300924609)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (73, 1), (1776739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (73, 1), (1776739, 1)] : List FactorBlock).map factorBlockValue).prod) = 8300924609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_73
      · exact prime_oneHundredThirtyNineEG_1776739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8300924609) ^ 4150462304 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8300924609) ^ 113711296 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8300924609) ^ 4672 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_8408205187 : Nat.Prime 8408205187 := by
  apply lucas_primality 8408205187 (2 : ZMod 8408205187)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1401367531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1401367531, 1)] : List FactorBlock).map factorBlockValue).prod) = 8408205187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_1401367531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8408205187) ^ 4204102593 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8408205187) ^ 2802735062 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8408205187) ^ 6 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_8652222841 : Nat.Prime 8652222841 := by
  apply lucas_primality 8652222841 (14 : ZMod 8652222841)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (72101857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (72101857, 1)] : List FactorBlock).map factorBlockValue).prod) = 8652222841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_72101857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 8652222841) ^ 4326111420 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8652222841) ^ 2884074280 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8652222841) ^ 1730444568 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8652222841) ^ 120 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_11216527999 : Nat.Prime 11216527999 := by
  apply lucas_primality 11216527999 (3 : ZMod 11216527999)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (5501, 1), (26141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (5501, 1), (26141, 1)] : List FactorBlock).map factorBlockValue).prod) = 11216527999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_5501
      · exact prime_oneHundredThirtyNineEG_26141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11216527999) ^ 5608263999 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11216527999) ^ 3738842666 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11216527999) ^ 862809846 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11216527999) ^ 2038998 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11216527999) ^ 429078 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_11336012687 : Nat.Prime 11336012687 := by
  apply lucas_primality 11336012687 (5 : ZMod 11336012687)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (131814101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (131814101, 1)] : List FactorBlock).map factorBlockValue).prod) = 11336012687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_43
      · exact prime_oneHundredThirtyNineEG_131814101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11336012687) ^ 5668006343 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11336012687) ^ 263628202 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 11336012687) ^ 86 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_11414002441 : Nat.Prime 11414002441 := by
  apply lucas_primality 11414002441 (11 : ZMod 11414002441)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (107, 1), (167, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (107, 1), (167, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) = 11414002441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_107
      · exact prime_oneHundredThirtyNineEG_167
      · exact prime_oneHundredThirtyNineEG_5323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11414002441) ^ 5707001220 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 11414002441) ^ 3804667480 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 11414002441) ^ 2282800488 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 11414002441) ^ 106672920 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 11414002441) ^ 68347320 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 11414002441) ^ 2144280 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_11842086811 : Nat.Prime 11842086811 := by
  apply lucas_primality 11842086811 (10 : ZMod 11842086811)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (394736227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (394736227, 1)] : List FactorBlock).map factorBlockValue).prod) = 11842086811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_394736227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 11842086811) ^ 5921043405 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 11842086811) ^ 3947362270 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 11842086811) ^ 2368417362 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 11842086811) ^ 30 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_12847717079 : Nat.Prime 12847717079 := by
  apply lucas_primality 12847717079 (13 : ZMod 12847717079)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1019, 1), (900583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1019, 1), (900583, 1)] : List FactorBlock).map factorBlockValue).prod) = 12847717079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_1019
      · exact prime_oneHundredThirtyNineEG_900583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 12847717079) ^ 6423858539 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 12847717079) ^ 1835388154 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 12847717079) ^ 12608162 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 12847717079) ^ 14266 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_13054553483 : Nat.Prime 13054553483 := by
  apply lucas_primality 13054553483 (2 : ZMod 13054553483)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6527276741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6527276741, 1)] : List FactorBlock).map factorBlockValue).prod) = 13054553483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_6527276741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 13054553483) ^ 6527276741 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13054553483) ^ 2 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_13612797571 : Nat.Prime 13612797571 := by
  apply lucas_primality 13612797571 (3 : ZMod 13612797571)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (23882101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (23882101, 1)] : List FactorBlock).map factorBlockValue).prod) = 13612797571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_23882101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13612797571) ^ 6806398785 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13612797571) ^ 4537599190 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13612797571) ^ 2722559514 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13612797571) ^ 716463030 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13612797571) ^ 570 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_14963778839 : Nat.Prime 14963778839 := by
  apply lucas_primality 14963778839 (7 : ZMod 14963778839)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (2239, 1), (42299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (2239, 1), (42299, 1)] : List FactorBlock).map factorBlockValue).prod) = 14963778839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_79
      · exact prime_oneHundredThirtyNineEG_2239
      · exact prime_oneHundredThirtyNineEG_42299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14963778839) ^ 7481889419 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 14963778839) ^ 189414922 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 14963778839) ^ 6683242 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 14963778839) ^ 353762 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_15688481927 : Nat.Prime 15688481927 := by
  apply lucas_primality 15688481927 (5 : ZMod 15688481927)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (17, 1), (929, 1), (2939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (17, 1), (929, 1), (2939, 1)] : List FactorBlock).map factorBlockValue).prod) = 15688481927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_929
      · exact prime_oneHundredThirtyNineEG_2939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15688481927) ^ 7844240963 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15688481927) ^ 1206806302 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15688481927) ^ 922851878 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15688481927) ^ 16887494 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15688481927) ^ 5338034 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_17870858051 : Nat.Prime 17870858051 := by
  apply lucas_primality 17870858051 (2 : ZMod 17870858051)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (43, 1), (97, 1), (85691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (43, 1), (97, 1), (85691, 1)] : List FactorBlock).map factorBlockValue).prod) = 17870858051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_43
      · exact prime_oneHundredThirtyNineEG_97
      · exact prime_oneHundredThirtyNineEG_85691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17870858051) ^ 8935429025 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17870858051) ^ 3574171610 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17870858051) ^ 415601350 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17870858051) ^ 184235650 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17870858051) ^ 208550 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_22268953541 : Nat.Prime 22268953541 := by
  apply lucas_primality 22268953541 (2 : ZMod 22268953541)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (1307, 1), (27481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (1307, 1), (27481, 1)] : List FactorBlock).map factorBlockValue).prod) = 22268953541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_31
      · exact prime_oneHundredThirtyNineEG_1307
      · exact prime_oneHundredThirtyNineEG_27481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22268953541) ^ 11134476770 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22268953541) ^ 4453790708 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22268953541) ^ 718353340 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22268953541) ^ 17038220 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22268953541) ^ 810340 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_23003717797 : Nat.Prime 23003717797 := by
  apply lucas_primality 23003717797 (2 : ZMod 23003717797)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (70999129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (70999129, 1)] : List FactorBlock).map factorBlockValue).prod) = 23003717797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_70999129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23003717797) ^ 11501858898 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23003717797) ^ 7667905932 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23003717797) ^ 324 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_25799719723 : Nat.Prime 25799719723 := by
  apply lucas_primality 25799719723 (12 : ZMod 25799719723)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (614279041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (614279041, 1)] : List FactorBlock).map factorBlockValue).prod) = 25799719723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_614279041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 25799719723) ^ 12899859861 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (12 : ZMod 25799719723) ^ 8599906574 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (12 : ZMod 25799719723) ^ 3685674246 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (12 : ZMod 25799719723) ^ 42 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_33740362871 : Nat.Prime 33740362871 := by
  apply lucas_primality 33740362871 (13 : ZMod 33740362871)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1163, 1), (1373, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1163, 1), (1373, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) = 33740362871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_1163
      · exact prime_oneHundredThirtyNineEG_1373
      · exact prime_oneHundredThirtyNineEG_2113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 33740362871) ^ 16870181435 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 33740362871) ^ 6748072574 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 33740362871) ^ 29011490 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 33740362871) ^ 24574190 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 33740362871) ^ 15967990 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_42349041521 : Nat.Prime 42349041521 := by
  apply lucas_primality 42349041521 (3 : ZMod 42349041521)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1091, 1), (485209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1091, 1), (485209, 1)] : List FactorBlock).map factorBlockValue).prod) = 42349041521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_1091
      · exact prime_oneHundredThirtyNineEG_485209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42349041521) ^ 21174520760 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 42349041521) ^ 8469808304 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 42349041521) ^ 38816720 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 42349041521) ^ 87280 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_43311587491 : Nat.Prime 43311587491 := by
  apply lucas_primality 43311587491 (17 : ZMod 43311587491)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (160413287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (160413287, 1)] : List FactorBlock).map factorBlockValue).prod) = 43311587491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_160413287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 43311587491) ^ 21655793745 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 43311587491) ^ 14437195830 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 43311587491) ^ 8662317498 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 43311587491) ^ 270 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_49598728889 : Nat.Prime 49598728889 := by
  apply lucas_primality 49598728889 (3 : ZMod 49598728889)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (131911513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (131911513, 1)] : List FactorBlock).map factorBlockValue).prod) = 49598728889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_131911513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49598728889) ^ 24799364444 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 49598728889) ^ 1055292104 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 49598728889) ^ 376 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_49751311627 : Nat.Prime 49751311627 := by
  apply lucas_primality 49751311627 (2 : ZMod 49751311627)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2843, 1), (972199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2843, 1), (972199, 1)] : List FactorBlock).map factorBlockValue).prod) = 49751311627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_2843
      · exact prime_oneHundredThirtyNineEG_972199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49751311627) ^ 24875655813 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49751311627) ^ 16583770542 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49751311627) ^ 17499582 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49751311627) ^ 51174 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_57342969083 : Nat.Prime 57342969083 := by
  apply lucas_primality 57342969083 (5 : ZMod 57342969083)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (5981, 1), (16703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (5981, 1), (16703, 1)] : List FactorBlock).map factorBlockValue).prod) = 57342969083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_41
      · exact prime_oneHundredThirtyNineEG_5981
      · exact prime_oneHundredThirtyNineEG_16703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57342969083) ^ 28671484541 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 57342969083) ^ 8191852726 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 57342969083) ^ 1398609002 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 57342969083) ^ 9587522 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 57342969083) ^ 3433094 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_68421459307 : Nat.Prime 68421459307 := by
  apply lucas_primality 68421459307 (2 : ZMod 68421459307)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (719, 1), (45707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (719, 1), (45707, 1)] : List FactorBlock).map factorBlockValue).prod) = 68421459307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_347
      · exact prime_oneHundredThirtyNineEG_719
      · exact prime_oneHundredThirtyNineEG_45707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68421459307) ^ 34210729653 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 68421459307) ^ 22807153102 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 68421459307) ^ 197179998 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 68421459307) ^ 95161974 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 68421459307) ^ 1496958 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_80035888697 : Nat.Prime 80035888697 := by
  apply lucas_primality 80035888697 (3 : ZMod 80035888697)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (127, 1), (78775481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (127, 1), (78775481, 1)] : List FactorBlock).map factorBlockValue).prod) = 80035888697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_127
      · exact prime_oneHundredThirtyNineEG_78775481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 80035888697) ^ 40017944348 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 80035888697) ^ 630203848 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 80035888697) ^ 1016 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_110701963373 : Nat.Prime 110701963373 := by
  apply lucas_primality 110701963373 (2 : ZMod 110701963373)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (13, 1), (37, 1), (747239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (13, 1), (37, 1), (747239, 1)] : List FactorBlock).map factorBlockValue).prod) = 110701963373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_747239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 110701963373) ^ 55350981686 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110701963373) ^ 15814566196 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110701963373) ^ 10063814852 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110701963373) ^ 8515535644 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110701963373) ^ 2991944956 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 110701963373) ^ 148148 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_120657597961 : Nat.Prime 120657597961 := by
  apply lucas_primality 120657597961 (17 : ZMod 120657597961)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (109, 1), (401069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (109, 1), (401069, 1)] : List FactorBlock).map factorBlockValue).prod) = 120657597961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_109
      · exact prime_oneHundredThirtyNineEG_401069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 120657597961) ^ 60328798980 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 120657597961) ^ 40219199320 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 120657597961) ^ 24131519592 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 120657597961) ^ 5245982520 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 120657597961) ^ 1106950440 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (17 : ZMod 120657597961) ^ 300840 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_125082266809 : Nat.Prime 125082266809 := by
  apply lucas_primality 125082266809 (7 : ZMod 125082266809)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5211761117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5211761117, 1)] : List FactorBlock).map factorBlockValue).prod) = 125082266809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5211761117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 125082266809) ^ 62541133404 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 125082266809) ^ 41694088936 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 125082266809) ^ 24 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_125314554221 : Nat.Prime 125314554221 := by
  apply lucas_primality 125314554221 (2 : ZMod 125314554221)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79, 1), (79313009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79, 1), (79313009, 1)] : List FactorBlock).map factorBlockValue).prod) = 125314554221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_79
      · exact prime_oneHundredThirtyNineEG_79313009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 125314554221) ^ 62657277110 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 125314554221) ^ 25062910844 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 125314554221) ^ 1586260180 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 125314554221) ^ 1580 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_129571818983 : Nat.Prime 129571818983 := by
  apply lucas_primality 129571818983 (5 : ZMod 129571818983)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (67, 1), (1511, 1), (22067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (67, 1), (1511, 1), (22067, 1)] : List FactorBlock).map factorBlockValue).prod) = 129571818983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_67
      · exact prime_oneHundredThirtyNineEG_1511
      · exact prime_oneHundredThirtyNineEG_22067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 129571818983) ^ 64785909491 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 129571818983) ^ 4467993758 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 129571818983) ^ 1933907746 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 129571818983) ^ 85752362 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 129571818983) ^ 5871746 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_140117421011 : Nat.Prime 140117421011 := by
  apply lucas_primality 140117421011 (7 : ZMod 140117421011)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2001677443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2001677443, 1)] : List FactorBlock).map factorBlockValue).prod) = 140117421011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_2001677443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 140117421011) ^ 70058710505 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 140117421011) ^ 28023484202 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 140117421011) ^ 20016774430 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 140117421011) ^ 70 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_145058718487 : Nat.Prime 145058718487 := by
  apply lucas_primality 145058718487 (3 : ZMod 145058718487)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (3413, 1), (33893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (3413, 1), (33893, 1)] : List FactorBlock).map factorBlockValue).prod) = 145058718487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_3413
      · exact prime_oneHundredThirtyNineEG_33893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 145058718487) ^ 72529359243 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 145058718487) ^ 48352906162 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 145058718487) ^ 13187156226 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 145058718487) ^ 7634669394 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 145058718487) ^ 42501822 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 145058718487) ^ 4279902 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_185691986941 : Nat.Prime 185691986941 := by
  apply lucas_primality 185691986941 (2 : ZMod 185691986941)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3094866449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3094866449, 1)] : List FactorBlock).map factorBlockValue).prod) = 185691986941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_3094866449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 185691986941) ^ 92845993470 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 185691986941) ^ 61897328980 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 185691986941) ^ 37138397388 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 185691986941) ^ 60 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_187019532727 : Nat.Prime 187019532727 := by
  apply lucas_primality 187019532727 (6 : ZMod 187019532727)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 3), (14187493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 3), (14187493, 1)] : List FactorBlock).map factorBlockValue).prod) = 187019532727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_14187493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 187019532727) ^ 93509766363 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 187019532727) ^ 62339844242 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 187019532727) ^ 14386117902 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 187019532727) ^ 13182 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_189285081917 : Nat.Prime 189285081917 := by
  apply lucas_primality 189285081917 (2 : ZMod 189285081917)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1237, 1), (5464981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1237, 1), (5464981, 1)] : List FactorBlock).map factorBlockValue).prod) = 189285081917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_1237
      · exact prime_oneHundredThirtyNineEG_5464981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 189285081917) ^ 94642540958 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 189285081917) ^ 27040725988 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 189285081917) ^ 153019468 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 189285081917) ^ 34636 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_211087867343 : Nat.Prime 211087867343 := by
  apply lucas_primality 211087867343 (10 : ZMod 211087867343)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (317, 1), (30267833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (317, 1), (30267833, 1)] : List FactorBlock).map factorBlockValue).prod) = 211087867343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_317
      · exact prime_oneHundredThirtyNineEG_30267833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 211087867343) ^ 105543933671 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 211087867343) ^ 19189806122 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 211087867343) ^ 665892326 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 211087867343) ^ 6974 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_212372264413 : Nat.Prime 212372264413 := by
  apply lucas_primality 212372264413 (6 : ZMod 212372264413)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (76613371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (76613371, 1)] : List FactorBlock).map factorBlockValue).prod) = 212372264413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_76613371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 212372264413) ^ 106186132206 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 212372264413) ^ 70790754804 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 212372264413) ^ 30338894916 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 212372264413) ^ 19306569492 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 212372264413) ^ 2772 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_223863750133 : Nat.Prime 223863750133 := by
  apply lucas_primality 223863750133 (2 : ZMod 223863750133)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (43, 1), (199, 1), (198193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (43, 1), (199, 1), (198193, 1)] : List FactorBlock).map factorBlockValue).prod) = 223863750133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_43
      · exact prime_oneHundredThirtyNineEG_199
      · exact prime_oneHundredThirtyNineEG_198193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 223863750133) ^ 111931875066 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 223863750133) ^ 74621250044 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 223863750133) ^ 20351250012 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 223863750133) ^ 5206133724 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 223863750133) ^ 1124943468 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 223863750133) ^ 1129524 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_259143637967 : Nat.Prime 259143637967 := by
  apply lucas_primality 259143637967 (5 : ZMod 259143637967)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (129571818983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (129571818983, 1)] : List FactorBlock).map factorBlockValue).prod) = 259143637967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_129571818983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 259143637967) ^ 129571818983 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 259143637967) ^ 2 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_269922902969 : Nat.Prime 269922902969 := by
  apply lucas_primality 269922902969 (3 : ZMod 269922902969)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (33740362871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (33740362871, 1)] : List FactorBlock).map factorBlockValue).prod) = 269922902969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_33740362871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 269922902969) ^ 134961451484 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 269922902969) ^ 8 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_270526866349 : Nat.Prime 270526866349 := by
  apply lucas_primality 270526866349 (2 : ZMod 270526866349)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (191, 1), (3807449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (191, 1), (3807449, 1)] : List FactorBlock).map factorBlockValue).prod) = 270526866349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_31
      · exact prime_oneHundredThirtyNineEG_191
      · exact prime_oneHundredThirtyNineEG_3807449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 270526866349) ^ 135263433174 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270526866349) ^ 90175622116 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270526866349) ^ 8726673108 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270526866349) ^ 1416371028 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270526866349) ^ 71052 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_313974983797 : Nat.Prime 313974983797 := by
  apply lucas_primality 313974983797 (2 : ZMod 313974983797)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (67, 1), (271, 1), (62653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (67, 1), (271, 1), (62653, 1)] : List FactorBlock).map factorBlockValue).prod) = 313974983797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_67
      · exact prime_oneHundredThirtyNineEG_271
      · exact prime_oneHundredThirtyNineEG_62653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 313974983797) ^ 156987491898 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 313974983797) ^ 104658327932 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 313974983797) ^ 13651086252 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 313974983797) ^ 4686193788 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 313974983797) ^ 1158579276 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 313974983797) ^ 5011332 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_315435135143 : Nat.Prime 315435135143 := by
  apply lucas_primality 315435135143 (5 : ZMod 315435135143)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (8300924609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (8300924609, 1)] : List FactorBlock).map factorBlockValue).prod) = 315435135143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_8300924609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 315435135143) ^ 157717567571 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 315435135143) ^ 16601849218 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 315435135143) ^ 38 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_363865253267 : Nat.Prime 363865253267 := by
  apply lucas_primality 363865253267 (2 : ZMod 363865253267)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (307, 1), (6109427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (307, 1), (6109427, 1)] : List FactorBlock).map factorBlockValue).prod) = 363865253267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_97
      · exact prime_oneHundredThirtyNineEG_307
      · exact prime_oneHundredThirtyNineEG_6109427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 363865253267) ^ 181932626633 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 363865253267) ^ 3751188178 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 363865253267) ^ 1185228838 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 363865253267) ^ 59558 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_401474366701 : Nat.Prime 401474366701 := by
  apply lucas_primality 401474366701 (2 : ZMod 401474366701)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (1367, 1), (88997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (1367, 1), (88997, 1)] : List FactorBlock).map factorBlockValue).prod) = 401474366701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_1367
      · exact prime_oneHundredThirtyNineEG_88997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 401474366701) ^ 200737183350 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 401474366701) ^ 133824788900 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 401474366701) ^ 80294873340 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 401474366701) ^ 36497669700 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 401474366701) ^ 293690100 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 401474366701) ^ 4511100 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_406518401411 : Nat.Prime 406518401411 := by
  apply lucas_primality 406518401411 (2 : ZMod 406518401411)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (335965621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (335965621, 1)] : List FactorBlock).map factorBlockValue).prod) = 406518401411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_335965621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 406518401411) ^ 203259200705 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 406518401411) ^ 81303680282 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 406518401411) ^ 36956218310 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 406518401411) ^ 1210 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_495698136697 : Nat.Prime 495698136697 := by
  apply lucas_primality 495698136697 (5 : ZMod 495698136697)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 3), (41, 1), (53, 1), (3079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 3), (41, 1), (53, 1), (3079, 1)] : List FactorBlock).map factorBlockValue).prod) = 495698136697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_41
      · exact prime_oneHundredThirtyNineEG_53
      · exact prime_oneHundredThirtyNineEG_3079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 495698136697) ^ 247849068348 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 495698136697) ^ 165232712232 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 495698136697) ^ 70814019528 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 495698136697) ^ 12090198456 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 495698136697) ^ 9352795032 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 495698136697) ^ 160993224 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_580234873949 : Nat.Prime 580234873949 := by
  apply lucas_primality 580234873949 (2 : ZMod 580234873949)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (145058718487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (145058718487, 1)] : List FactorBlock).map factorBlockValue).prod) = 580234873949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_145058718487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 580234873949) ^ 290117436974 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 580234873949) ^ 4 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_610130334497 : Nat.Prime 610130334497 := by
  apply lucas_primality 610130334497 (3 : ZMod 610130334497)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (919, 1), (20747087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (919, 1), (20747087, 1)] : List FactorBlock).map factorBlockValue).prod) = 610130334497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_919
      · exact prime_oneHundredThirtyNineEG_20747087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 610130334497) ^ 305065167248 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 610130334497) ^ 663906784 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 610130334497) ^ 29408 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_653414283409 : Nat.Prime 653414283409 := by
  apply lucas_primality 653414283409 (7 : ZMod 653414283409)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13612797571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13612797571, 1)] : List FactorBlock).map factorBlockValue).prod) = 653414283409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13612797571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 653414283409) ^ 326707141704 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 653414283409) ^ 217804761136 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 653414283409) ^ 48 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_920095558957 : Nat.Prime 920095558957 := by
  apply lucas_primality 920095558957 (6 : ZMod 920095558957)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (3651172853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (3651172853, 1)] : List FactorBlock).map factorBlockValue).prod) = 920095558957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_3651172853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 920095558957) ^ 460047779478 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 920095558957) ^ 306698519652 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 920095558957) ^ 131442222708 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 920095558957) ^ 252 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_992670175171 : Nat.Prime 992670175171 := by
  apply lucas_primality 992670175171 (2 : ZMod 992670175171)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (151, 1), (73044163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (151, 1), (73044163, 1)] : List FactorBlock).map factorBlockValue).prod) = 992670175171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_151
      · exact prime_oneHundredThirtyNineEG_73044163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 992670175171) ^ 496335087585 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 992670175171) ^ 330890058390 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 992670175171) ^ 198534035034 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 992670175171) ^ 6573974670 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 992670175171) ^ 13590 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1199255681137 : Nat.Prime 1199255681137 := by
  apply lucas_primality 1199255681137 (7 : ZMod 1199255681137)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1373, 1), (18197009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1373, 1), (18197009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1199255681137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_1373
      · exact prime_oneHundredThirtyNineEG_18197009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1199255681137) ^ 599627840568 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1199255681137) ^ 399751893712 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1199255681137) ^ 873456432 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1199255681137) ^ 65904 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1216232093231 : Nat.Prime 1216232093231 := by
  apply lucas_primality 1216232093231 (14 : ZMod 1216232093231)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (31, 1), (50952329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (31, 1), (50952329, 1)] : List FactorBlock).map factorBlockValue).prod) = 1216232093231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_31
      · exact prime_oneHundredThirtyNineEG_50952329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1216232093231) ^ 608116046615 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 1216232093231) ^ 243246418646 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 1216232093231) ^ 173747441890 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 1216232093231) ^ 110566553930 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 1216232093231) ^ 39233293330 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 1216232093231) ^ 23870 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1588492783243 : Nat.Prime 1588492783243 := by
  apply lucas_primality 1588492783243 (2 : ZMod 1588492783243)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (241, 1), (122060303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (241, 1), (122060303, 1)] : List FactorBlock).map factorBlockValue).prod) = 1588492783243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_241
      · exact prime_oneHundredThirtyNineEG_122060303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1588492783243) ^ 794246391621 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1588492783243) ^ 529497594414 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1588492783243) ^ 6591256362 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1588492783243) ^ 13014 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1595506370789 : Nat.Prime 1595506370789 := by
  apply lucas_primality 1595506370789 (2 : ZMod 1595506370789)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (167, 1), (6379, 1), (34039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (167, 1), (6379, 1), (34039, 1)] : List FactorBlock).map factorBlockValue).prod) = 1595506370789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_167
      · exact prime_oneHundredThirtyNineEG_6379
      · exact prime_oneHundredThirtyNineEG_34039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1595506370789) ^ 797753185394 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595506370789) ^ 145046033708 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595506370789) ^ 9553930364 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595506370789) ^ 250118572 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1595506370789) ^ 46872892 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1917070782637 : Nat.Prime 1917070782637 := by
  apply lucas_primality 1917070782637 (2 : ZMod 1917070782637)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (8408205187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (8408205187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1917070782637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_8408205187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1917070782637) ^ 958535391318 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1917070782637) ^ 639023594212 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1917070782637) ^ 100898462244 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1917070782637) ^ 228 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2111387973361 : Nat.Prime 2111387973361 := by
  apply lucas_primality 2111387973361 (11 : ZMod 2111387973361)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (29, 1), (10433, 1), (29077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (29, 1), (10433, 1), (29077, 1)] : List FactorBlock).map factorBlockValue).prod) = 2111387973361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_10433
      · exact prime_oneHundredThirtyNineEG_29077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2111387973361) ^ 1055693986680 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2111387973361) ^ 703795991120 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2111387973361) ^ 422277594672 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2111387973361) ^ 72806481840 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2111387973361) ^ 202375920 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2111387973361) ^ 72613680 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2144262375917 : Nat.Prime 2144262375917 := by
  apply lucas_primality 2144262375917 (2 : ZMod 2144262375917)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3709, 1), (144531031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3709, 1), (144531031, 1)] : List FactorBlock).map factorBlockValue).prod) = 2144262375917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3709
      · exact prime_oneHundredThirtyNineEG_144531031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2144262375917) ^ 1072131187958 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2144262375917) ^ 578124124 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2144262375917) ^ 14836 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2183191519603 : Nat.Prime 2183191519603 := by
  apply lucas_primality 2183191519603 (2 : ZMod 2183191519603)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (363865253267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (363865253267, 1)] : List FactorBlock).map factorBlockValue).prod) = 2183191519603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_363865253267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2183191519603) ^ 1091595759801 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2183191519603) ^ 727730506534 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2183191519603) ^ 6 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2218804223837 : Nat.Prime 2218804223837 := by
  apply lucas_primality 2218804223837 (2 : ZMod 2218804223837)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (6491, 1), (1203619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (6491, 1), (1203619, 1)] : List FactorBlock).map factorBlockValue).prod) = 2218804223837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_71
      · exact prime_oneHundredThirtyNineEG_6491
      · exact prime_oneHundredThirtyNineEG_1203619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2218804223837) ^ 1109402111918 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2218804223837) ^ 31250763716 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2218804223837) ^ 341827796 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2218804223837) ^ 1843444 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3161468725847 : Nat.Prime 3161468725847 := by
  apply lucas_primality 3161468725847 (5 : ZMod 3161468725847)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (223, 1), (5783, 1), (64513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (223, 1), (5783, 1), (64513, 1)] : List FactorBlock).map factorBlockValue).prod) = 3161468725847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_223
      · exact prime_oneHundredThirtyNineEG_5783
      · exact prime_oneHundredThirtyNineEG_64513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3161468725847) ^ 1580734362923 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3161468725847) ^ 166393090834 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3161468725847) ^ 14176989802 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3161468725847) ^ 546683162 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 3161468725847) ^ 49005142 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3460889136401 : Nat.Prime 3460889136401 := by
  apply lucas_primality 3460889136401 (3 : ZMod 3460889136401)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (8652222841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (8652222841, 1)] : List FactorBlock).map factorBlockValue).prod) = 3460889136401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_8652222841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3460889136401) ^ 1730444568200 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3460889136401) ^ 692177827280 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3460889136401) ^ 400 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4662745489427 : Nat.Prime 4662745489427 := by
  apply lucas_primality 4662745489427 (2 : ZMod 4662745489427)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (263, 1), (2803, 1), (3162517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (263, 1), (2803, 1), (3162517, 1)] : List FactorBlock).map factorBlockValue).prod) = 4662745489427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_263
      · exact prime_oneHundredThirtyNineEG_2803
      · exact prime_oneHundredThirtyNineEG_3162517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4662745489427) ^ 2331372744713 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4662745489427) ^ 17729070302 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4662745489427) ^ 1663483942 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4662745489427) ^ 1474378 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6754977991217 : Nat.Prime 6754977991217 := by
  apply lucas_primality 6754977991217 (5 : ZMod 6754977991217)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (9497, 1), (488513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (9497, 1), (488513, 1)] : List FactorBlock).map factorBlockValue).prod) = 6754977991217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_9497
      · exact prime_oneHundredThirtyNineEG_488513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6754977991217) ^ 3377488995608 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6754977991217) ^ 964996855888 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6754977991217) ^ 519613691632 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6754977991217) ^ 711274928 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6754977991217) ^ 13827632 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_7005655840567 : Nat.Prime 7005655840567 := by
  apply lucas_primality 7005655840567 (3 : ZMod 7005655840567)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (11336012687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (11336012687, 1)] : List FactorBlock).map factorBlockValue).prod) = 7005655840567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_103
      · exact prime_oneHundredThirtyNineEG_11336012687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7005655840567) ^ 3502827920283 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7005655840567) ^ 2335218613522 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7005655840567) ^ 68016076122 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7005655840567) ^ 618 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_8230555716241 : Nat.Prime 8230555716241 := by
  apply lucas_primality 8230555716241 (14 : ZMod 8230555716241)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (13, 1), (19, 1), (53, 1), (238151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (13, 1), (19, 1), (53, 1), (238151, 1)] : List FactorBlock).map factorBlockValue).prod) = 8230555716241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_53
      · exact prime_oneHundredThirtyNineEG_238151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 8230555716241) ^ 4115277858120 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8230555716241) ^ 2743518572080 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8230555716241) ^ 1646111143248 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8230555716241) ^ 748232337840 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8230555716241) ^ 633119670480 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8230555716241) ^ 433187142960 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8230555716241) ^ 155293504080 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 8230555716241) ^ 34560240 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_9522948179387 : Nat.Prime 9522948179387 := by
  apply lucas_primality 9522948179387 (2 : ZMod 9522948179387)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (907, 1), (6719, 1), (781321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (907, 1), (6719, 1), (781321, 1)] : List FactorBlock).map factorBlockValue).prod) = 9522948179387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_907
      · exact prime_oneHundredThirtyNineEG_6719
      · exact prime_oneHundredThirtyNineEG_781321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9522948179387) ^ 4761474089693 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9522948179387) ^ 10499391598 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9522948179387) ^ 1417316294 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9522948179387) ^ 12188266 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_9769124162999 : Nat.Prime 9769124162999 := by
  apply lucas_primality 9769124162999 (11 : ZMod 9769124162999)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (212372264413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (212372264413, 1)] : List FactorBlock).map factorBlockValue).prod) = 9769124162999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_212372264413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 9769124162999) ^ 4884562081499 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 9769124162999) ^ 424744528826 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 9769124162999) ^ 46 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_11647748618417 : Nat.Prime 11647748618417 := by
  apply lucas_primality 11647748618417 (3 : ZMod 11647748618417)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (359, 1), (2027811389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (359, 1), (2027811389, 1)] : List FactorBlock).map factorBlockValue).prod) = 11647748618417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_359
      · exact prime_oneHundredThirtyNineEG_2027811389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11647748618417) ^ 5823874309208 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11647748618417) ^ 32444982224 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11647748618417) ^ 5744 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_13792020801569 : Nat.Prime 13792020801569 := by
  apply lucas_primality 13792020801569 (3 : ZMod 13792020801569)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (79, 1), (188127739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (79, 1), (188127739, 1)] : List FactorBlock).map factorBlockValue).prod) = 13792020801569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_79
      · exact prime_oneHundredThirtyNineEG_188127739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13792020801569) ^ 6896010400784 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13792020801569) ^ 475586924192 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13792020801569) ^ 174582541792 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 13792020801569) ^ 73312 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_17154099007337 : Nat.Prime 17154099007337 := by
  apply lucas_primality 17154099007337 (3 : ZMod 17154099007337)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2144262375917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2144262375917, 1)] : List FactorBlock).map factorBlockValue).prod) = 17154099007337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_2144262375917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 17154099007337) ^ 8577049503668 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 17154099007337) ^ 8 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_19045041219187 : Nat.Prime 19045041219187 := by
  apply lucas_primality 19045041219187 (2 : ZMod 19045041219187)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 2), (83, 1), (197, 1), (69109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 2), (83, 1), (197, 1), (69109, 1)] : List FactorBlock).map factorBlockValue).prod) = 19045041219187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_53
      · exact prime_oneHundredThirtyNineEG_83
      · exact prime_oneHundredThirtyNineEG_197
      · exact prime_oneHundredThirtyNineEG_69109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19045041219187) ^ 9522520609593 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19045041219187) ^ 6348347073062 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19045041219187) ^ 359340400362 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19045041219187) ^ 229458327942 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19045041219187) ^ 96675336138 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19045041219187) ^ 275579754 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_20387692905457 : Nat.Prime 20387692905457 := by
  apply lucas_primality 20387692905457 (7 : ZMod 20387692905457)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (683, 1), (1847, 1), (14639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (683, 1), (1847, 1), (14639, 1)] : List FactorBlock).map factorBlockValue).prod) = 20387692905457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_683
      · exact prime_oneHundredThirtyNineEG_1847
      · exact prime_oneHundredThirtyNineEG_14639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20387692905457) ^ 10193846452728 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20387692905457) ^ 6795897635152 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20387692905457) ^ 886421430672 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20387692905457) ^ 29850209232 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20387692905457) ^ 11038274448 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 20387692905457) ^ 1392697104 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_29401304947129 : Nat.Prime 29401304947129 := by
  apply lucas_primality 29401304947129 (14 : ZMod 29401304947129)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (53, 1), (3037, 1), (845653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (53, 1), (3037, 1), (845653, 1)] : List FactorBlock).map factorBlockValue).prod) = 29401304947129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_53
      · exact prime_oneHundredThirtyNineEG_3037
      · exact prime_oneHundredThirtyNineEG_845653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 29401304947129) ^ 14700652473564 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 29401304947129) ^ 9800434982376 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 29401304947129) ^ 554741602776 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 29401304947129) ^ 9681035544 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (14 : ZMod 29401304947129) ^ 34767576 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_31948750829297 : Nat.Prime 31948750829297 := by
  apply lucas_primality 31948750829297 (3 : ZMod 31948750829297)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (59, 1), (15107, 1), (320041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (59, 1), (15107, 1), (320041, 1)] : List FactorBlock).map factorBlockValue).prod) = 31948750829297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_59
      · exact prime_oneHundredThirtyNineEG_15107
      · exact prime_oneHundredThirtyNineEG_320041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31948750829297) ^ 15974375414648 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31948750829297) ^ 4564107261328 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31948750829297) ^ 541504251344 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31948750829297) ^ 2114830928 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31948750829297) ^ 99827056 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_44424105630071 : Nat.Prime 44424105630071 := by
  apply lucas_primality 44424105630071 (13 : ZMod 44424105630071)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (21491, 1), (4398091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (21491, 1), (4398091, 1)] : List FactorBlock).map factorBlockValue).prod) = 44424105630071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_21491
      · exact prime_oneHundredThirtyNineEG_4398091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 44424105630071) ^ 22212052815035 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 44424105630071) ^ 8884821126014 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 44424105630071) ^ 945193736810 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 44424105630071) ^ 2067102770 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 44424105630071) ^ 10100770 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_49502775749027 : Nat.Prime 49502775749027 := by
  apply lucas_primality 49502775749027 (2 : ZMod 49502775749027)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (547, 1), (10559, 1), (4285381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (547, 1), (10559, 1), (4285381, 1)] : List FactorBlock).map factorBlockValue).prod) = 49502775749027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_547
      · exact prime_oneHundredThirtyNineEG_10559
      · exact prime_oneHundredThirtyNineEG_4285381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49502775749027) ^ 24751387874513 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49502775749027) ^ 90498675958 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49502775749027) ^ 4688206814 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 49502775749027) ^ 11551546 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_51426161733127 : Nat.Prime 51426161733127 := by
  apply lucas_primality 51426161733127 (3 : ZMod 51426161733127)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6803, 1), (1259889307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6803, 1), (1259889307, 1)] : List FactorBlock).map factorBlockValue).prod) = 51426161733127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_6803
      · exact prime_oneHundredThirtyNineEG_1259889307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51426161733127) ^ 25713080866563 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 51426161733127) ^ 17142053911042 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 51426161733127) ^ 7559335842 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 51426161733127) ^ 40818 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_76180164876749 : Nat.Prime 76180164876749 := by
  apply lucas_primality 76180164876749 (2 : ZMod 76180164876749)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19045041219187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19045041219187, 1)] : List FactorBlock).map factorBlockValue).prod) = 76180164876749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_19045041219187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 76180164876749) ^ 38090082438374 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 76180164876749) ^ 4 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_139019133959089 : Nat.Prime 139019133959089 := by
  apply lucas_primality 139019133959089 (11 : ZMod 139019133959089)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (10111, 1), (6986431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (10111, 1), (6986431, 1)] : List FactorBlock).map factorBlockValue).prod) = 139019133959089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_41
      · exact prime_oneHundredThirtyNineEG_10111
      · exact prime_oneHundredThirtyNineEG_6986431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 139019133959089) ^ 69509566979544 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 139019133959089) ^ 46339711319696 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 139019133959089) ^ 3390710584368 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 139019133959089) ^ 13749296208 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 139019133959089) ^ 19898448 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_199581949849859 : Nat.Prime 199581949849859 := by
  apply lucas_primality 199581949849859 (2 : ZMod 199581949849859)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1291, 1), (1571, 1), (49202689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1291, 1), (1571, 1), (49202689, 1)] : List FactorBlock).map factorBlockValue).prod) = 199581949849859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_1291
      · exact prime_oneHundredThirtyNineEG_1571
      · exact prime_oneHundredThirtyNineEG_49202689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 199581949849859) ^ 99790974924929 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 199581949849859) ^ 154594848838 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 199581949849859) ^ 127041342998 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 199581949849859) ^ 4056322 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_220111475307631 : Nat.Prime 220111475307631 := by
  apply lucas_primality 220111475307631 (3 : ZMod 220111475307631)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (368507, 1), (865661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (368507, 1), (865661, 1)] : List FactorBlock).map factorBlockValue).prod) = 220111475307631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_368507
      · exact prime_oneHundredThirtyNineEG_865661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 220111475307631) ^ 110055737653815 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 220111475307631) ^ 73370491769210 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 220111475307631) ^ 44022295061526 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 220111475307631) ^ 9570064143810 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 220111475307631) ^ 597306090 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 220111475307631) ^ 254269830 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_220488471495049 : Nat.Prime 220488471495049 := by
  apply lucas_primality 220488471495049 (11 : ZMod 220488471495049)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (4273, 1), (4421, 1), (28607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (4273, 1), (4421, 1), (28607, 1)] : List FactorBlock).map factorBlockValue).prod) = 220488471495049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_4273
      · exact prime_oneHundredThirtyNineEG_4421
      · exact prime_oneHundredThirtyNineEG_28607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 220488471495049) ^ 110244235747524 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 220488471495049) ^ 73496157165016 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 220488471495049) ^ 12969910087944 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 220488471495049) ^ 51600391176 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 220488471495049) ^ 49872986088 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 220488471495049) ^ 7707500664 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_274819570463257 : Nat.Prime 274819570463257 := by
  apply lucas_primality 274819570463257 (11 : ZMod 274819570463257)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (8623, 1), (14592733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (8623, 1), (14592733, 1)] : List FactorBlock).map factorBlockValue).prod) = 274819570463257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_8623
      · exact prime_oneHundredThirtyNineEG_14592733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 274819570463257) ^ 137409785231628 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 274819570463257) ^ 91606523487752 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 274819570463257) ^ 39259938637608 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 274819570463257) ^ 21139966958712 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 274819570463257) ^ 31870528872 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 274819570463257) ^ 18832632 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_321020617690723 : Nat.Prime 321020617690723 := by
  apply lucas_primality 321020617690723 (3 : ZMod 321020617690723)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (223863750133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (223863750133, 1)] : List FactorBlock).map factorBlockValue).prod) = 321020617690723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_239
      · exact prime_oneHundredThirtyNineEG_223863750133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 321020617690723) ^ 160510308845361 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 321020617690723) ^ 107006872563574 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 321020617690723) ^ 1343182500798 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 321020617690723) ^ 1434 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_364030780417643 : Nat.Prime 364030780417643 := by
  apply lucas_primality 364030780417643 (2 : ZMod 364030780417643)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (4243, 1), (3299831219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (4243, 1), (3299831219, 1)] : List FactorBlock).map factorBlockValue).prod) = 364030780417643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_4243
      · exact prime_oneHundredThirtyNineEG_3299831219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 364030780417643) ^ 182015390208821 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 364030780417643) ^ 28002367724434 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 364030780417643) ^ 85795611694 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 364030780417643) ^ 110318 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_396003120264491 : Nat.Prime 396003120264491 := by
  apply lucas_primality 396003120264491 (2 : ZMod 396003120264491)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (197, 1), (34981, 1), (5746457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (197, 1), (34981, 1), (5746457, 1)] : List FactorBlock).map factorBlockValue).prod) = 396003120264491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_197
      · exact prime_oneHundredThirtyNineEG_34981
      · exact prime_oneHundredThirtyNineEG_5746457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 396003120264491) ^ 198001560132245 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 396003120264491) ^ 79200624052898 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 396003120264491) ^ 2010168123170 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 396003120264491) ^ 11320520290 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 396003120264491) ^ 68912570 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_463638127907551 : Nat.Prime 463638127907551 := by
  apply lucas_primality 463638127907551 (6 : ZMod 463638127907551)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (439697, 1), (7029661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (439697, 1), (7029661, 1)] : List FactorBlock).map factorBlockValue).prod) = 463638127907551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_439697
      · exact prime_oneHundredThirtyNineEG_7029661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 463638127907551) ^ 231819063953775 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 463638127907551) ^ 154546042635850 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 463638127907551) ^ 92727625581510 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 463638127907551) ^ 1054449150 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 463638127907551) ^ 65954550 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_485700497565859 : Nat.Prime 485700497565859 := by
  apply lucas_primality 485700497565859 (2 : ZMod 485700497565859)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (23, 1), (23003717797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (23, 1), (23003717797, 1)] : List FactorBlock).map factorBlockValue).prod) = 485700497565859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_23003717797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 485700497565859) ^ 242850248782929 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 485700497565859) ^ 161900165855286 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 485700497565859) ^ 28570617503874 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 485700497565859) ^ 21117412937646 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 485700497565859) ^ 21114 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_584551457418433 : Nat.Prime 584551457418433 := by
  apply lucas_primality 584551457418433 (5 : ZMod 584551457418433)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 2), (37, 1), (47, 1), (35729411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 2), (37, 1), (47, 1), (35729411, 1)] : List FactorBlock).map factorBlockValue).prod) = 584551457418433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_35729411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 584551457418433) ^ 292275728709216 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 584551457418433) ^ 194850485806144 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 584551457418433) ^ 83507351059776 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 584551457418433) ^ 15798688038336 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 584551457418433) ^ 12437265051456 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 584551457418433) ^ 16360512 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_804543456589921 : Nat.Prime 804543456589921 := by
  apply lucas_primality 804543456589921 (7 : ZMod 804543456589921)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (17, 1), (101, 1), (277, 1), (1174727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (17, 1), (101, 1), (277, 1), (1174727, 1)] : List FactorBlock).map factorBlockValue).prod) = 804543456589921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_101
      · exact prime_oneHundredThirtyNineEG_277
      · exact prime_oneHundredThirtyNineEG_1174727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 804543456589921) ^ 402271728294960 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 804543456589921) ^ 268181152196640 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 804543456589921) ^ 160908691317984 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 804543456589921) ^ 47326085681760 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 804543456589921) ^ 7965776797920 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 804543456589921) ^ 2904489012960 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 804543456589921) ^ 684876960 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1327838012493743 : Nat.Prime 1327838012493743 := by
  apply lucas_primality 1327838012493743 (5 : ZMod 1327838012493743)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (87877, 1), (260520487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (87877, 1), (260520487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1327838012493743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_87877
      · exact prime_oneHundredThirtyNineEG_260520487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1327838012493743) ^ 663919006246871 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1327838012493743) ^ 45787517672198 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1327838012493743) ^ 15110188246 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1327838012493743) ^ 5096866 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1717370708970571 : Nat.Prime 1717370708970571 := by
  apply lucas_primality 1717370708970571 (7 : ZMod 1717370708970571)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (491, 1), (2711395363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (491, 1), (2711395363, 1)] : List FactorBlock).map factorBlockValue).prod) = 1717370708970571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_43
      · exact prime_oneHundredThirtyNineEG_491
      · exact prime_oneHundredThirtyNineEG_2711395363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1717370708970571) ^ 858685354485285 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717370708970571) ^ 572456902990190 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717370708970571) ^ 343474141794114 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717370708970571) ^ 39938853696990 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717370708970571) ^ 3497700018270 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717370708970571) ^ 633390 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1960719201299107 : Nat.Prime 1960719201299107 := by
  apply lucas_primality 1960719201299107 (2 : ZMod 1960719201299107)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1361, 1), (80035888697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1361, 1), (80035888697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1960719201299107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_1361
      · exact prime_oneHundredThirtyNineEG_80035888697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1960719201299107) ^ 980359600649553 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1960719201299107) ^ 653573067099702 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1960719201299107) ^ 1440645996546 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1960719201299107) ^ 24498 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2040929880151577 : Nat.Prime 2040929880151577 := by
  apply lucas_primality 2040929880151577 (3 : ZMod 2040929880151577)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (257, 1), (992670175171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (257, 1), (992670175171, 1)] : List FactorBlock).map factorBlockValue).prod) = 2040929880151577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_257
      · exact prime_oneHundredThirtyNineEG_992670175171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2040929880151577) ^ 1020464940075788 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2040929880151577) ^ 7941361401368 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2040929880151577) ^ 2056 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2120820860243273 : Nat.Prime 2120820860243273 := by
  apply lucas_primality 2120820860243273 (3 : ZMod 2120820860243273)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (193847, 1), (124326077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (193847, 1), (124326077, 1)] : List FactorBlock).map factorBlockValue).prod) = 2120820860243273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_193847
      · exact prime_oneHundredThirtyNineEG_124326077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2120820860243273) ^ 1060410430121636 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2120820860243273) ^ 192801896385752 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2120820860243273) ^ 10940694776 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2120820860243273) ^ 17058536 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2338688994747311 : Nat.Prime 2338688994747311 := by
  apply lucas_primality 2338688994747311 (13 : ZMod 2338688994747311)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15629, 1), (14963778839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15629, 1), (14963778839, 1)] : List FactorBlock).map factorBlockValue).prod) = 2338688994747311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_15629
      · exact prime_oneHundredThirtyNineEG_14963778839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2338688994747311) ^ 1169344497373655 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2338688994747311) ^ 467737798949462 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2338688994747311) ^ 149637788390 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 2338688994747311) ^ 156290 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2712531220325831 : Nat.Prime 2712531220325831 := by
  apply lucas_primality 2712531220325831 (7 : ZMod 2712531220325831)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (397, 1), (458039, 1), (1491701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (397, 1), (458039, 1), (1491701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2712531220325831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_397
      · exact prime_oneHundredThirtyNineEG_458039
      · exact prime_oneHundredThirtyNineEG_1491701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2712531220325831) ^ 1356265610162915 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2712531220325831) ^ 542506244065166 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2712531220325831) ^ 6832572343390 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2712531220325831) ^ 5922052970 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 2712531220325831) ^ 1818414830 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3097052546225093 : Nat.Prime 3097052546225093 := by
  apply lucas_primality 3097052546225093 (2 : ZMod 3097052546225093)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (1382237, 1), (6155519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (1382237, 1), (6155519, 1)] : List FactorBlock).map factorBlockValue).prod) = 3097052546225093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_1382237
      · exact prime_oneHundredThirtyNineEG_6155519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3097052546225093) ^ 1548526273112546 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097052546225093) ^ 442436078032156 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097052546225093) ^ 238234811248084 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097052546225093) ^ 2240608916 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3097052546225093) ^ 503134268 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4629044530067473 : Nat.Prime 4629044530067473 := by
  apply lucas_primality 4629044530067473 (5 : ZMod 4629044530067473)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (257, 1), (125082266809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (257, 1), (125082266809, 1)] : List FactorBlock).map factorBlockValue).prod) = 4629044530067473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_257
      · exact prime_oneHundredThirtyNineEG_125082266809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4629044530067473) ^ 2314522265033736 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4629044530067473) ^ 1543014843355824 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4629044530067473) ^ 18011846420496 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 4629044530067473) ^ 37008 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4991616075388961 : Nat.Prime 4991616075388961 := by
  apply lucas_primality 4991616075388961 (3 : ZMod 4991616075388961)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (17, 1), (37, 1), (49598728889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (17, 1), (37, 1), (49598728889, 1)] : List FactorBlock).map factorBlockValue).prod) = 4991616075388961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_49598728889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4991616075388961) ^ 2495808037694480 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4991616075388961) ^ 998323215077792 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4991616075388961) ^ 293624475022880 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4991616075388961) ^ 134908542578080 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4991616075388961) ^ 100640 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_5425062440651663 : Nat.Prime 5425062440651663 := by
  apply lucas_primality 5425062440651663 (5 : ZMod 5425062440651663)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2712531220325831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2712531220325831, 1)] : List FactorBlock).map factorBlockValue).prod) = 5425062440651663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_2712531220325831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 5425062440651663) ^ 2712531220325831 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 5425062440651663) ^ 2 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_5686285520649089 : Nat.Prime 5686285520649089 := by
  apply lucas_primality 5686285520649089 (3 : ZMod 5686285520649089)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (44424105630071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (44424105630071, 1)] : List FactorBlock).map factorBlockValue).prod) = 5686285520649089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_44424105630071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5686285520649089) ^ 2843142760324544 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5686285520649089) ^ 128 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6153633033018241 : Nat.Prime 6153633033018241 := by
  apply lucas_primality 6153633033018241 (29 : ZMod 6153633033018241)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (7, 1), (11, 1), (829, 1), (859, 1), (58451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (7, 1), (11, 1), (829, 1), (859, 1), (58451, 1)] : List FactorBlock).map factorBlockValue).prod) = 6153633033018241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_829
      · exact prime_oneHundredThirtyNineEG_859
      · exact prime_oneHundredThirtyNineEG_58451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 6153633033018241) ^ 3076816516509120 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (29 : ZMod 6153633033018241) ^ 2051211011006080 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (29 : ZMod 6153633033018241) ^ 1230726606603648 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (29 : ZMod 6153633033018241) ^ 879090433288320 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (29 : ZMod 6153633033018241) ^ 559421184819840 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (29 : ZMod 6153633033018241) ^ 7422959026560 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (29 : ZMod 6153633033018241) ^ 7163717151360 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (29 : ZMod 6153633033018241) ^ 105278490240 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6384107433948557 : Nat.Prime 6384107433948557 := by
  apply lucas_primality 6384107433948557 (2 : ZMod 6384107433948557)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (2141, 1), (57342969083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (2141, 1), (57342969083, 1)] : List FactorBlock).map factorBlockValue).prod) = 6384107433948557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_2141
      · exact prime_oneHundredThirtyNineEG_57342969083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6384107433948557) ^ 3192053716974278 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6384107433948557) ^ 491085187226812 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6384107433948557) ^ 2981834392316 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6384107433948557) ^ 111332 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6509051867313773 : Nat.Prime 6509051867313773 := by
  apply lucas_primality 6509051867313773 (2 : ZMod 6509051867313773)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (571, 1), (20089, 1), (20265871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (571, 1), (20089, 1), (20265871, 1)] : List FactorBlock).map factorBlockValue).prod) = 6509051867313773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_571
      · exact prime_oneHundredThirtyNineEG_20089
      · exact prime_oneHundredThirtyNineEG_20265871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6509051867313773) ^ 3254525933656886 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6509051867313773) ^ 929864552473396 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6509051867313773) ^ 11399390310532 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6509051867313773) ^ 324010745548 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6509051867313773) ^ 321182932 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_11313755581287941 : Nat.Prime 11313755581287941 := by
  apply lucas_primality 11313755581287941 (2 : ZMod 11313755581287941)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (51426161733127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (51426161733127, 1)] : List FactorBlock).map factorBlockValue).prod) = 11313755581287941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_51426161733127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11313755581287941) ^ 5656877790643970 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11313755581287941) ^ 2262751116257588 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11313755581287941) ^ 1028523234662540 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11313755581287941) ^ 220 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_13473130734733717 : Nat.Prime 13473130734733717 := by
  apply lucas_primality 13473130734733717 (2 : ZMod 13473130734733717)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2671, 1), (140117421011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2671, 1), (140117421011, 1)] : List FactorBlock).map factorBlockValue).prod) = 13473130734733717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_2671
      · exact prime_oneHundredThirtyNineEG_140117421011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13473130734733717) ^ 6736565367366858 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13473130734733717) ^ 4491043578244572 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13473130734733717) ^ 5044227156396 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13473130734733717) ^ 96156 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_15435062558816041 : Nat.Prime 15435062558816041 := by
  apply lucas_primality 15435062558816041 (13 : ZMod 15435062558816041)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (43, 1), (5051, 1), (28200839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (43, 1), (5051, 1), (28200839, 1)] : List FactorBlock).map factorBlockValue).prod) = 15435062558816041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_43
      · exact prime_oneHundredThirtyNineEG_5051
      · exact prime_oneHundredThirtyNineEG_28200839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 15435062558816041) ^ 7717531279408020 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 15435062558816041) ^ 5145020852938680 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 15435062558816041) ^ 3087012511763208 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 15435062558816041) ^ 2205008936973720 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 15435062558816041) ^ 358954943228280 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 15435062558816041) ^ 3055842914040 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 15435062558816041) ^ 547326360 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_17536543722552991 : Nat.Prime 17536543722552991 := by
  apply lucas_primality 17536543722552991 (3 : ZMod 17536543722552991)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (584551457418433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (584551457418433, 1)] : List FactorBlock).map factorBlockValue).prod) = 17536543722552991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_584551457418433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17536543722552991) ^ 8768271861276495 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 17536543722552991) ^ 5845514574184330 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 17536543722552991) ^ 3507308744510598 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 17536543722552991) ^ 30 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_23143575180095333 : Nat.Prime 23143575180095333 := by
  apply lucas_primality 23143575180095333 (2 : ZMod 23143575180095333)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (607, 1), (120657597961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (607, 1), (120657597961, 1)] : List FactorBlock).map factorBlockValue).prod) = 23143575180095333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_79
      · exact prime_oneHundredThirtyNineEG_607
      · exact prime_oneHundredThirtyNineEG_120657597961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23143575180095333) ^ 11571787590047666 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23143575180095333) ^ 292956647849308 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23143575180095333) ^ 38127800955676 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23143575180095333) ^ 191812 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_35639047048343509 : Nat.Prime 35639047048343509 := by
  apply lucas_primality 35639047048343509 (2 : ZMod 35639047048343509)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (3391, 1), (1263815893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (3391, 1), (1263815893, 1)] : List FactorBlock).map factorBlockValue).prod) = 35639047048343509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_3391
      · exact prime_oneHundredThirtyNineEG_1263815893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35639047048343509) ^ 17819523524171754 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35639047048343509) ^ 11879682349447836 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35639047048343509) ^ 5091292435477644 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35639047048343509) ^ 3239913368031228 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35639047048343509) ^ 10509892966188 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 35639047048343509) ^ 28199556 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_90770622267418789 : Nat.Prime 90770622267418789 := by
  apply lucas_primality 90770622267418789 (2 : ZMod 90770622267418789)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2235239, 1), (3384075941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2235239, 1), (3384075941, 1)] : List FactorBlock).map factorBlockValue).prod) = 90770622267418789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_2235239
      · exact prime_oneHundredThirtyNineEG_3384075941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90770622267418789) ^ 45385311133709394 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 90770622267418789) ^ 30256874089139596 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 90770622267418789) ^ 40608911292 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 90770622267418789) ^ 26822868 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_97289272085972903 : Nat.Prime 97289272085972903 := by
  apply lucas_primality 97289272085972903 (5 : ZMod 97289272085972903)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (220111475307631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (220111475307631, 1)] : List FactorBlock).map factorBlockValue).prod) = 97289272085972903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_220111475307631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 97289272085972903) ^ 48644636042986451 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 97289272085972903) ^ 7483790160459454 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 97289272085972903) ^ 5722898357998406 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 97289272085972903) ^ 442 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_102442318437469601 : Nat.Prime 102442318437469601 := by
  apply lucas_primality 102442318437469601 (3 : ZMod 102442318437469601)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (37, 1), (3460889136401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (37, 1), (3460889136401, 1)] : List FactorBlock).map factorBlockValue).prod) = 102442318437469601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_3460889136401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102442318437469601) ^ 51221159218734800 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 102442318437469601) ^ 20488463687493920 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 102442318437469601) ^ 2768711309120800 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 102442318437469601) ^ 29600 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_246145321320729641 : Nat.Prime 246145321320729641 := by
  apply lucas_primality 246145321320729641 (3 : ZMod 246145321320729641)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (6153633033018241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (6153633033018241, 1)] : List FactorBlock).map factorBlockValue).prod) = 246145321320729641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_6153633033018241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 246145321320729641) ^ 123072660660364820 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 246145321320729641) ^ 49229064264145928 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 246145321320729641) ^ 40 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_327974254661310821 : Nat.Prime 327974254661310821 := by
  apply lucas_primality 327974254661310821 (2 : ZMod 327974254661310821)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (41, 1), (13792020801569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (41, 1), (13792020801569, 1)] : List FactorBlock).map factorBlockValue).prod) = 327974254661310821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_41
      · exact prime_oneHundredThirtyNineEG_13792020801569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 327974254661310821) ^ 163987127330655410 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 327974254661310821) ^ 65594850932262164 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 327974254661310821) ^ 11309457057286580 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 327974254661310821) ^ 7999372064910020 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 327974254661310821) ^ 23780 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_371120556228484511 : Nat.Prime 371120556228484511 := by
  apply lucas_primality 371120556228484511 (7 : ZMod 371120556228484511)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2579, 1), (23081, 1), (89065807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2579, 1), (23081, 1), (89065807, 1)] : List FactorBlock).map factorBlockValue).prod) = 371120556228484511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_2579
      · exact prime_oneHundredThirtyNineEG_23081
      · exact prime_oneHundredThirtyNineEG_89065807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 371120556228484511) ^ 185560278114242255 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 371120556228484511) ^ 74224111245696902 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 371120556228484511) ^ 53017222318354930 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 371120556228484511) ^ 143900952395690 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 371120556228484511) ^ 16079050137710 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 371120556228484511) ^ 4166812930 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_474037307103769181 : Nat.Prime 474037307103769181 := by
  apply lucas_primality 474037307103769181 (2 : ZMod 474037307103769181)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (130706879, 1), (181336021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (130706879, 1), (181336021, 1)] : List FactorBlock).map factorBlockValue).prod) = 474037307103769181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_130706879
      · exact prime_oneHundredThirtyNineEG_181336021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 474037307103769181) ^ 237018653551884590 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 474037307103769181) ^ 94807461420753836 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 474037307103769181) ^ 3626720420 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 474037307103769181) ^ 2614137580 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_489066886850639813 : Nat.Prime 489066886850639813 := by
  apply lucas_primality 489066886850639813 (2 : ZMod 489066886850639813)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (13, 1), (19, 1), (73, 1), (44017, 1), (1273159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (13, 1), (19, 1), (73, 1), (44017, 1), (1273159, 1)] : List FactorBlock).map factorBlockValue).prod) = 489066886850639813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_73
      · exact prime_oneHundredThirtyNineEG_44017
      · exact prime_oneHundredThirtyNineEG_1273159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 489066886850639813) ^ 244533443425319906 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 489066886850639813) ^ 44460626077330892 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 489066886850639813) ^ 37620529757741524 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 489066886850639813) ^ 25740362465823148 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 489066886850639813) ^ 6699546395214244 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 489066886850639813) ^ 11110863685636 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 489066886850639813) ^ 384136535068 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_494017556833905277 : Nat.Prime 494017556833905277 := by
  apply lucas_primality 494017556833905277 (5 : ZMod 494017556833905277)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2624099, 1), (15688481927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2624099, 1), (15688481927, 1)] : List FactorBlock).map factorBlockValue).prod) = 494017556833905277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_2624099
      · exact prime_oneHundredThirtyNineEG_15688481927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 494017556833905277) ^ 247008778416952638 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 494017556833905277) ^ 164672518944635092 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 494017556833905277) ^ 188261783124 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 494017556833905277) ^ 31489188 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_739986116310781513 : Nat.Prime 739986116310781513 := by
  apply lucas_primality 739986116310781513 (5 : ZMod 739986116310781513)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (31, 1), (2029, 1), (25799719723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (31, 1), (2029, 1), (25799719723, 1)] : List FactorBlock).map factorBlockValue).prod) = 739986116310781513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_31
      · exact prime_oneHundredThirtyNineEG_2029
      · exact prime_oneHundredThirtyNineEG_25799719723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 739986116310781513) ^ 369993058155390756 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 739986116310781513) ^ 246662038770260504 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 739986116310781513) ^ 38946637700567448 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 739986116310781513) ^ 23870519880992952 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 739986116310781513) ^ 364704838004328 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 739986116310781513) ^ 28681944 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_944075596789902971 : Nat.Prime 944075596789902971 := by
  apply lucas_primality 944075596789902971 (2 : ZMod 944075596789902971)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113, 1), (121867, 1), (6855548507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113, 1), (121867, 1), (6855548507, 1)] : List FactorBlock).map factorBlockValue).prod) = 944075596789902971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_113
      · exact prime_oneHundredThirtyNineEG_121867
      · exact prime_oneHundredThirtyNineEG_6855548507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 944075596789902971) ^ 472037798394951485 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 944075596789902971) ^ 188815119357980594 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 944075596789902971) ^ 8354651299025690 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 944075596789902971) ^ 7746769812910 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 944075596789902971) ^ 137709710 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1013113127987340763 : Nat.Prime 1013113127987340763 := by
  apply lucas_primality 1013113127987340763 (2 : ZMod 1013113127987340763)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15053873, 1), (11216527999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15053873, 1), (11216527999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1013113127987340763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_15053873
      · exact prime_oneHundredThirtyNineEG_11216527999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1013113127987340763) ^ 506556563993670381 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1013113127987340763) ^ 337704375995780254 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1013113127987340763) ^ 67299167994 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1013113127987340763) ^ 90323238 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1477909392242418913 : Nat.Prime 1477909392242418913 := by
  apply lucas_primality 1477909392242418913 (15 : ZMod 1477909392242418913)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (2254927, 1), (975317573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (2254927, 1), (975317573, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477909392242418913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_2254927
      · exact prime_oneHundredThirtyNineEG_975317573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 1477909392242418913) ^ 738954696121209456 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (15 : ZMod 1477909392242418913) ^ 492636464080806304 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (15 : ZMod 1477909392242418913) ^ 211129913177488416 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (15 : ZMod 1477909392242418913) ^ 655413409056 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (15 : ZMod 1477909392242418913) ^ 1515310944 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1883342693760762887 : Nat.Prime 1883342693760762887 := by
  apply lucas_primality 1883342693760762887 (5 : ZMod 1883342693760762887)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (587, 1), (1319, 1), (1216232093231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (587, 1), (1319, 1), (1216232093231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1883342693760762887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_587
      · exact prime_oneHundredThirtyNineEG_1319
      · exact prime_oneHundredThirtyNineEG_1216232093231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1883342693760762887) ^ 941671346880381443 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1883342693760762887) ^ 3208420261943378 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1883342693760762887) ^ 1427856477453194 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1883342693760762887) ^ 1548506 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1994023348740590117 : Nat.Prime 1994023348740590117 := by
  apply lucas_primality 1994023348740590117 (2 : ZMod 1994023348740590117)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (13473130734733717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (13473130734733717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1994023348740590117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_13473130734733717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1994023348740590117) ^ 997011674370295058 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1994023348740590117) ^ 53892522938934868 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1994023348740590117) ^ 148 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2481211292039080873 : Nat.Prime 2481211292039080873 := by
  apply lucas_primality 2481211292039080873 (10 : ZMod 2481211292039080873)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (2393, 1), (1390069, 1), (1635761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (2393, 1), (1390069, 1), (1635761, 1)] : List FactorBlock).map factorBlockValue).prod) = 2481211292039080873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_2393
      · exact prime_oneHundredThirtyNineEG_1390069
      · exact prime_oneHundredThirtyNineEG_1635761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2481211292039080873) ^ 1240605646019540436 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 2481211292039080873) ^ 827070430679693624 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 2481211292039080873) ^ 130590068002056888 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 2481211292039080873) ^ 1036862219824104 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 2481211292039080873) ^ 1784955489288 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (10 : ZMod 2481211292039080873) ^ 1516854413352 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2844223842622615087 : Nat.Prime 2844223842622615087 := by
  apply lucas_primality 2844223842622615087 (3 : ZMod 2844223842622615087)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (474037307103769181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (474037307103769181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2844223842622615087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_474037307103769181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2844223842622615087) ^ 1422111921311307543 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2844223842622615087) ^ 948074614207538362 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2844223842622615087) ^ 6 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4596862943550149627 : Nat.Prime 4596862943550149627 := by
  apply lucas_primality 4596862943550149627 (2 : ZMod 4596862943550149627)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (739, 1), (2657, 1), (18217, 1), (64256743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (739, 1), (2657, 1), (18217, 1), (64256743, 1)] : List FactorBlock).map factorBlockValue).prod) = 4596862943550149627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_739
      · exact prime_oneHundredThirtyNineEG_2657
      · exact prime_oneHundredThirtyNineEG_18217
      · exact prime_oneHundredThirtyNineEG_64256743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4596862943550149627) ^ 2298431471775074813 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4596862943550149627) ^ 6220382873545534 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4596862943550149627) ^ 1730095198927418 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4596862943550149627) ^ 252339185571178 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4596862943550149627) ^ 71538996982 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_8682649099776818443 : Nat.Prime 8682649099776818443 := by
  apply lucas_primality 8682649099776818443 (2 : ZMod 8682649099776818443)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (281, 1), (8527, 1), (11842086811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (281, 1), (8527, 1), (11842086811, 1)] : List FactorBlock).map factorBlockValue).prod) = 8682649099776818443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_281
      · exact prime_oneHundredThirtyNineEG_8527
      · exact prime_oneHundredThirtyNineEG_11842086811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8682649099776818443) ^ 4341324549888409221 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8682649099776818443) ^ 2894216366592272814 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8682649099776818443) ^ 510744064692754026 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8682649099776818443) ^ 30899107116643482 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8682649099776818443) ^ 1018253676530646 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 8682649099776818443) ^ 733202622 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_9186307961495977903 : Nat.Prime 9186307961495977903 := by
  apply lucas_primality 9186307961495977903 (3 : ZMod 9186307961495977903)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (798641, 1), (1917070782637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (798641, 1), (1917070782637, 1)] : List FactorBlock).map factorBlockValue).prod) = 9186307961495977903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_798641
      · exact prime_oneHundredThirtyNineEG_1917070782637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9186307961495977903) ^ 4593153980747988951 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9186307961495977903) ^ 3062102653831992634 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9186307961495977903) ^ 11502424695822 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9186307961495977903) ^ 4791846 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_9303076312089536917 : Nat.Prime 9303076312089536917 := by
  apply lucas_primality 9303076312089536917 (2 : ZMod 9303076312089536917)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (29, 1), (7901, 1), (125314554221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (29, 1), (7901, 1), (125314554221, 1)] : List FactorBlock).map factorBlockValue).prod) = 9303076312089536917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_7901
      · exact prime_oneHundredThirtyNineEG_125314554221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9303076312089536917) ^ 4651538156044768458 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9303076312089536917) ^ 3101025437363178972 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9303076312089536917) ^ 320795734899639204 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9303076312089536917) ^ 1177455551460516 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 9303076312089536917) ^ 74237796 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_10852097168518630217 : Nat.Prime 10852097168518630217 := by
  apply lucas_primality 10852097168518630217 (3 : ZMod 10852097168518630217)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (227, 1), (853, 1), (7005655840567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (227, 1), (853, 1), (7005655840567, 1)] : List FactorBlock).map factorBlockValue).prod) = 10852097168518630217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_227
      · exact prime_oneHundredThirtyNineEG_853
      · exact prime_oneHundredThirtyNineEG_7005655840567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10852097168518630217) ^ 5426048584259315108 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10852097168518630217) ^ 47806595456029208 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10852097168518630217) ^ 12722271006469672 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 10852097168518630217) ^ 1549048 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_12245544798078052361 : Nat.Prime 12245544798078052361 := by
  apply lucas_primality 12245544798078052361 (3 : ZMod 12245544798078052361)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (43, 1), (307, 1), (619, 1), (95279, 1), (393209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (43, 1), (307, 1), (619, 1), (95279, 1), (393209, 1)] : List FactorBlock).map factorBlockValue).prod) = 12245544798078052361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_43
      · exact prime_oneHundredThirtyNineEG_307
      · exact prime_oneHundredThirtyNineEG_619
      · exact prime_oneHundredThirtyNineEG_95279
      · exact prime_oneHundredThirtyNineEG_393209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12245544798078052361) ^ 6122772399039026180 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12245544798078052361) ^ 2449108959615610472 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12245544798078052361) ^ 284780111583210520 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12245544798078052361) ^ 39887768071915480 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12245544798078052361) ^ 19782786426620440 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12245544798078052361) ^ 128523019742840 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 12245544798078052361) ^ 31142585236040 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_14779093922424189131 : Nat.Prime 14779093922424189131 := by
  apply lucas_primality 14779093922424189131 (2 : ZMod 14779093922424189131)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1477909392242418913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1477909392242418913, 1)] : List FactorBlock).map factorBlockValue).prod) = 14779093922424189131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_1477909392242418913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14779093922424189131) ^ 7389546961212094565 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14779093922424189131) ^ 2955818784484837826 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14779093922424189131) ^ 10 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_19803021659524584407 : Nat.Prime 19803021659524584407 := by
  apply lucas_primality 19803021659524584407 (5 : ZMod 19803021659524584407)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (51199, 1), (381103, 1), (10796917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (51199, 1), (381103, 1), (10796917, 1)] : List FactorBlock).map factorBlockValue).prod) = 19803021659524584407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_51199
      · exact prime_oneHundredThirtyNineEG_381103
      · exact prime_oneHundredThirtyNineEG_10796917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19803021659524584407) ^ 9901510829762292203 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 19803021659524584407) ^ 421340886372863498 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 19803021659524584407) ^ 386785321188394 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 19803021659524584407) ^ 51962387227402 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 19803021659524584407) ^ 1834136694718 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_55715538635071614799 : Nat.Prime 55715538635071614799 := by
  apply lucas_primality 55715538635071614799 (3 : ZMod 55715538635071614799)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3187, 1), (18973, 1), (140419, 1), (1093657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3187, 1), (18973, 1), (140419, 1), (1093657, 1)] : List FactorBlock).map factorBlockValue).prod) = 55715538635071614799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_3187
      · exact prime_oneHundredThirtyNineEG_18973
      · exact prime_oneHundredThirtyNineEG_140419
      · exact prime_oneHundredThirtyNineEG_1093657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55715538635071614799) ^ 27857769317535807399 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55715538635071614799) ^ 18571846211690538266 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55715538635071614799) ^ 17482126964252154 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55715538635071614799) ^ 2936569790495526 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55715538635071614799) ^ 396780625378842 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 55715538635071614799) ^ 50944252754814 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_58356836509590770923 : Nat.Prime 58356836509590770923 := by
  apply lucas_primality 58356836509590770923 (13 : ZMod 58356836509590770923)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (251, 1), (274819570463257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (251, 1), (274819570463257, 1)] : List FactorBlock).map factorBlockValue).prod) = 58356836509590770923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_47
      · exact prime_oneHundredThirtyNineEG_251
      · exact prime_oneHundredThirtyNineEG_274819570463257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 58356836509590770923) ^ 29178418254795385461 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 58356836509590770923) ^ 19452278836530256974 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 58356836509590770923) ^ 1241634819352995126 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 58356836509590770923) ^ 232497356611915422 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (13 : ZMod 58356836509590770923) ^ 212346 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_85758551877720999373 : Nat.Prime 85758551877720999373 := by
  apply lucas_primality 85758551877720999373 (2 : ZMod 85758551877720999373)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1193, 1), (22193, 1), (269922902969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1193, 1), (22193, 1), (269922902969, 1)] : List FactorBlock).map factorBlockValue).prod) = 85758551877720999373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_1193
      · exact prime_oneHundredThirtyNineEG_22193
      · exact prime_oneHundredThirtyNineEG_269922902969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85758551877720999373) ^ 42879275938860499686 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85758551877720999373) ^ 28586183959240333124 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85758551877720999373) ^ 71884787827092204 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85758551877720999373) ^ 3864216278904204 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 85758551877720999373) ^ 317714988 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_107071852464239146229 : Nat.Prime 107071852464239146229 := by
  apply lucas_primality 107071852464239146229 (2 : ZMod 107071852464239146229)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6949, 1), (56299, 1), (68421459307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6949, 1), (56299, 1), (68421459307, 1)] : List FactorBlock).map factorBlockValue).prod) = 107071852464239146229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_6949
      · exact prime_oneHundredThirtyNineEG_56299
      · exact prime_oneHundredThirtyNineEG_68421459307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107071852464239146229) ^ 53535926232119573114 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 107071852464239146229) ^ 15408238950099172 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 107071852464239146229) ^ 1901842882897372 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 107071852464239146229) ^ 1564887004 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_108572848880842038487 : Nat.Prime 108572848880842038487 := by
  apply lucas_primality 108572848880842038487 (3 : ZMod 108572848880842038487)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (489066886850639813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (489066886850639813, 1)] : List FactorBlock).map factorBlockValue).prod) = 108572848880842038487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_37
      · exact prime_oneHundredThirtyNineEG_489066886850639813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 108572848880842038487) ^ 54286424440421019243 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 108572848880842038487) ^ 36190949626947346162 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 108572848880842038487) ^ 2934401321103838878 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 108572848880842038487) ^ 222 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_197445320252374796473 : Nat.Prime 197445320252374796473 := by
  apply lucas_primality 197445320252374796473 (5 : ZMod 197445320252374796473)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (41, 1), (15435062558816041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (41, 1), (15435062558816041, 1)] : List FactorBlock).map factorBlockValue).prod) = 197445320252374796473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_41
      · exact prime_oneHundredThirtyNineEG_15435062558816041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 197445320252374796473) ^ 98722660126187398236 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 197445320252374796473) ^ 65815106750791598824 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 197445320252374796473) ^ 15188101557874984344 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 197445320252374796473) ^ 4815739518350604792 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 197445320252374796473) ^ 12792 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_283754077563275054159 : Nat.Prime 283754077563275054159 := by
  apply lucas_primality 283754077563275054159 (7 : ZMod 283754077563275054159)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (16836271, 1), (495698136697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (16836271, 1), (495698136697, 1)] : List FactorBlock).map factorBlockValue).prod) = 283754077563275054159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_16836271
      · exact prime_oneHundredThirtyNineEG_495698136697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 283754077563275054159) ^ 141877038781637527079 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 283754077563275054159) ^ 16691416327251473774 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 283754077563275054159) ^ 16853736647698 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 283754077563275054159) ^ 572433214 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_306192161772760399337 : Nat.Prime 306192161772760399337 := by
  apply lucas_primality 306192161772760399337 (3 : ZMod 306192161772760399337)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3761, 1), (4334497, 1), (2347805101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3761, 1), (4334497, 1), (2347805101, 1)] : List FactorBlock).map factorBlockValue).prod) = 306192161772760399337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3761
      · exact prime_oneHundredThirtyNineEG_4334497
      · exact prime_oneHundredThirtyNineEG_2347805101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 306192161772760399337) ^ 153096080886380199668 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 306192161772760399337) ^ 81412433334953576 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 306192161772760399337) ^ 70640759878888 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 306192161772760399337) ^ 130416345736 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_856623147569068344043 : Nat.Prime 856623147569068344043 := by
  apply lucas_primality 856623147569068344043 (2 : ZMod 856623147569068344043)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14992261, 1), (9522948179387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14992261, 1), (9522948179387, 1)] : List FactorBlock).map factorBlockValue).prod) = 856623147569068344043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_14992261
      · exact prime_oneHundredThirtyNineEG_9522948179387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 856623147569068344043) ^ 428311573784534172021 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 856623147569068344043) ^ 285541049189689448014 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 856623147569068344043) ^ 57137689076322 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 856623147569068344043) ^ 89953566 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1108969212933376726793 : Nat.Prime 1108969212933376726793 := by
  apply lucas_primality 1108969212933376726793 (3 : ZMod 1108969212933376726793)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19803021659524584407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19803021659524584407, 1)] : List FactorBlock).map factorBlockValue).prod) = 1108969212933376726793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_19803021659524584407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1108969212933376726793) ^ 554484606466688363396 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1108969212933376726793) ^ 158424173276196675256 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1108969212933376726793) ^ 56 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2954088526221451428737 : Nat.Prime 2954088526221451428737 := by
  apply lucas_primality 2954088526221451428737 (3 : ZMod 2954088526221451428737)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (827, 1), (42709, 1), (653414283409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (827, 1), (42709, 1), (653414283409, 1)] : List FactorBlock).map factorBlockValue).prod) = 2954088526221451428737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_827
      · exact prime_oneHundredThirtyNineEG_42709
      · exact prime_oneHundredThirtyNineEG_653414283409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2954088526221451428737) ^ 1477044263110725714368 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2954088526221451428737) ^ 3572053840654717568 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2954088526221451428737) ^ 69167822384543104 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2954088526221451428737) ^ 4521003904 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_3313869771241836598117 : Nat.Prime 3313869771241836598117 := by
  apply lucas_primality 3313869771241836598117 (2 : ZMod 3313869771241836598117)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (43, 1), (494017556833905277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (43, 1), (494017556833905277, 1)] : List FactorBlock).map factorBlockValue).prod) = 3313869771241836598117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_43
      · exact prime_oneHundredThirtyNineEG_494017556833905277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3313869771241836598117) ^ 1656934885620918299058 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3313869771241836598117) ^ 1104623257080612199372 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3313869771241836598117) ^ 254913059326295122932 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3313869771241836598117) ^ 77066738866089223212 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3313869771241836598117) ^ 6708 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_6795335173359089613937 : Nat.Prime 6795335173359089613937 := by
  apply lucas_primality 6795335173359089613937 (5 : ZMod 6795335173359089613937)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (229, 1), (349, 1), (853, 1), (81637, 1), (25437397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (229, 1), (349, 1), (853, 1), (81637, 1), (25437397, 1)] : List FactorBlock).map factorBlockValue).prod) = 6795335173359089613937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_229
      · exact prime_oneHundredThirtyNineEG_349
      · exact prime_oneHundredThirtyNineEG_853
      · exact prime_oneHundredThirtyNineEG_81637
      · exact prime_oneHundredThirtyNineEG_25437397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6795335173359089613937) ^ 3397667586679544806968 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6795335173359089613937) ^ 2265111724453029871312 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6795335173359089613937) ^ 29673952722092094384 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6795335173359089613937) ^ 19470874422232348464 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6795335173359089613937) ^ 7966395279436212912 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6795335173359089613937) ^ 83238423427601328 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 6795335173359089613937) ^ 267139565159088 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_7446599590152573633841 : Nat.Prime 7446599590152573633841 := by
  apply lucas_primality 7446599590152573633841 (23 : ZMod 7446599590152573633841)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (626783, 1), (49502775749027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (626783, 1), (49502775749027, 1)] : List FactorBlock).map factorBlockValue).prod) = 7446599590152573633841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_626783
      · exact prime_oneHundredThirtyNineEG_49502775749027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 7446599590152573633841) ^ 3723299795076286816920 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (23 : ZMod 7446599590152573633841) ^ 2482199863384191211280 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (23 : ZMod 7446599590152573633841) ^ 1489319918030514726768 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (23 : ZMod 7446599590152573633841) ^ 11880666179766480 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (23 : ZMod 7446599590152573633841) ^ 150427920 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_9108831944535475476151 : Nat.Prime 9108831944535475476151 := by
  apply lucas_primality 9108831944535475476151 (6 : ZMod 9108831944535475476151)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (223, 1), (90770622267418789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (223, 1), (90770622267418789, 1)] : List FactorBlock).map factorBlockValue).prod) = 9108831944535475476151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_223
      · exact prime_oneHundredThirtyNineEG_90770622267418789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9108831944535475476151) ^ 4554415972267737738075 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9108831944535475476151) ^ 3036277314845158492050 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9108831944535475476151) ^ 1821766388907095095230 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9108831944535475476151) ^ 40846780020338455050 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 9108831944535475476151) ^ 100350 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_12942074486506442675947 : Nat.Prime 12942074486506442675947 := by
  apply lucas_primality 12942074486506442675947 (2 : ZMod 12942074486506442675947)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (123001, 1), (17536543722552991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (123001, 1), (17536543722552991, 1)] : List FactorBlock).map factorBlockValue).prod) = 12942074486506442675947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_123001
      · exact prime_oneHundredThirtyNineEG_17536543722552991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12942074486506442675947) ^ 6471037243253221337973 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12942074486506442675947) ^ 4314024828835480891982 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12942074486506442675947) ^ 105219262335317946 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12942074486506442675947) ^ 738006 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_14697223765092499168177 : Nat.Prime 14697223765092499168177 := by
  apply lucas_primality 14697223765092499168177 (7 : ZMod 14697223765092499168177)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (306192161772760399337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (306192161772760399337, 1)] : List FactorBlock).map factorBlockValue).prod) = 14697223765092499168177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_306192161772760399337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 14697223765092499168177) ^ 7348611882546249584088 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 14697223765092499168177) ^ 4899074588364166389392 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (7 : ZMod 14697223765092499168177) ^ 48 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_14971628936163813987683 : Nat.Prime 14971628936163813987683 := by
  apply lucas_primality 14971628936163813987683 (2 : ZMod 14971628936163813987683)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (431, 1), (2481211292039080873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (431, 1), (2481211292039080873, 1)] : List FactorBlock).map factorBlockValue).prod) = 14971628936163813987683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_431
      · exact prime_oneHundredThirtyNineEG_2481211292039080873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14971628936163813987683) ^ 7485814468081906993841 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14971628936163813987683) ^ 2138804133737687712526 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14971628936163813987683) ^ 34736958088547132222 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14971628936163813987683) ^ 6034 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_17809096791578509956397 : Nat.Prime 17809096791578509956397 := by
  apply lucas_primality 17809096791578509956397 (5 : ZMod 17809096791578509956397)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (29, 1), (187224509, 1), (1911454271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (29, 1), (187224509, 1), (1911454271, 1)] : List FactorBlock).map factorBlockValue).prod) = 17809096791578509956397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_187224509
      · exact prime_oneHundredThirtyNineEG_1911454271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17809096791578509956397) ^ 8904548395789254978198 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17809096791578509956397) ^ 5936365597192836652132 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17809096791578509956397) ^ 1619008799234409996036 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17809096791578509956397) ^ 1369930522429116150492 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17809096791578509956397) ^ 614106785916500343324 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17809096791578509956397) ^ 95121610342044 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 17809096791578509956397) ^ 9317040465876 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_19891066338975030898291 : Nat.Prime 19891066338975030898291 := by
  apply lucas_primality 19891066338975030898291 (2 : ZMod 19891066338975030898291)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (611922887, 1), (13054553483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (611922887, 1), (13054553483, 1)] : List FactorBlock).map factorBlockValue).prod) = 19891066338975030898291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_83
      · exact prime_oneHundredThirtyNineEG_611922887
      · exact prime_oneHundredThirtyNineEG_13054553483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19891066338975030898291) ^ 9945533169487515449145 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19891066338975030898291) ^ 6630355446325010299430 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19891066338975030898291) ^ 3978213267795006179658 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19891066338975030898291) ^ 239651401674397962630 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19891066338975030898291) ^ 32505838172670 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19891066338975030898291) ^ 1523687988630 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_27891049715114198608067 : Nat.Prime 27891049715114198608067 := by
  apply lucas_primality 27891049715114198608067 (2 : ZMod 27891049715114198608067)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8737, 1), (266863, 1), (1274921, 1), (4691383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8737, 1), (266863, 1), (1274921, 1), (4691383, 1)] : List FactorBlock).map factorBlockValue).prod) = 27891049715114198608067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_8737
      · exact prime_oneHundredThirtyNineEG_266863
      · exact prime_oneHundredThirtyNineEG_1274921
      · exact prime_oneHundredThirtyNineEG_4691383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27891049715114198608067) ^ 13945524857557099304033 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 27891049715114198608067) ^ 3192291371765388418 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 27891049715114198608067) ^ 104514487640153182 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 27891049715114198608067) ^ 21876688606677746 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 27891049715114198608067) ^ 5945165789089102 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_31369573944092825980921 : Nat.Prime 31369573944092825980921 := by
  apply lucas_primality 31369573944092825980921 (11 : ZMod 31369573944092825980921)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (211, 1), (1873, 1), (220488471495049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (211, 1), (1873, 1), (220488471495049, 1)] : List FactorBlock).map factorBlockValue).prod) = 31369573944092825980921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_211
      · exact prime_oneHundredThirtyNineEG_1873
      · exact prime_oneHundredThirtyNineEG_220488471495049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 31369573944092825980921) ^ 15684786972046412990460 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 31369573944092825980921) ^ 10456524648030941993640 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 31369573944092825980921) ^ 6273914788818565196184 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 31369573944092825980921) ^ 148670966559681639720 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 31369573944092825980921) ^ 16748304294763922040 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 31369573944092825980921) ^ 142273080 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_53291445482071831587029 : Nat.Prime 53291445482071831587029 := by
  apply lucas_primality 53291445482071831587029 (2 : ZMod 53291445482071831587029)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1433357, 1), (1327838012493743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1433357, 1), (1327838012493743, 1)] : List FactorBlock).map factorBlockValue).prod) = 53291445482071831587029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_1433357
      · exact prime_oneHundredThirtyNineEG_1327838012493743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53291445482071831587029) ^ 26645722741035915793514 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 53291445482071831587029) ^ 7613063640295975941004 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 53291445482071831587029) ^ 37179464349824804 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 53291445482071831587029) ^ 40133996 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_144405416542437441278369 : Nat.Prime 144405416542437441278369 := by
  apply lucas_primality 144405416542437441278369 (3 : ZMod 144405416542437441278369)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (503, 1), (9059, 1), (76180164876749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (503, 1), (9059, 1), (76180164876749, 1)] : List FactorBlock).map factorBlockValue).prod) = 144405416542437441278369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_503
      · exact prime_oneHundredThirtyNineEG_9059
      · exact prime_oneHundredThirtyNineEG_76180164876749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 144405416542437441278369) ^ 72202708271218720639184 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144405416542437441278369) ^ 11108108964802880098336 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144405416542437441278369) ^ 287088303265283183456 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144405416542437441278369) ^ 15940547140129974752 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144405416542437441278369) ^ 1895577632 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_161470608299066871130229 : Nat.Prime 161470608299066871130229 := by
  apply lucas_primality 161470608299066871130229 (2 : ZMod 161470608299066871130229)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (6947, 1), (529355549, 1), (1568161117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (6947, 1), (529355549, 1), (1568161117, 1)] : List FactorBlock).map factorBlockValue).prod) = 161470608299066871130229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_6947
      · exact prime_oneHundredThirtyNineEG_529355549
      · exact prime_oneHundredThirtyNineEG_1568161117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161470608299066871130229) ^ 80735304149533435565114 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161470608299066871130229) ^ 23067229757009553018604 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161470608299066871130229) ^ 23243214092279670524 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161470608299066871130229) ^ 305032427834372 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 161470608299066871130229) ^ 102968123969284 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_382318680270921410913133 : Nat.Prime 382318680270921410913133 := by
  apply lucas_primality 382318680270921410913133 (5 : ZMod 382318680270921410913133)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (909529, 1), (11364973, 1), (3082189333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (909529, 1), (11364973, 1), (3082189333, 1)] : List FactorBlock).map factorBlockValue).prod) = 382318680270921410913133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_909529
      · exact prime_oneHundredThirtyNineEG_11364973
      · exact prime_oneHundredThirtyNineEG_3082189333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 382318680270921410913133) ^ 191159340135460705456566 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 382318680270921410913133) ^ 127439560090307136971044 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 382318680270921410913133) ^ 420347982605196108 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 382318680270921410913133) ^ 33640086982249884 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 382318680270921410913133) ^ 124041270332604 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_406039371947738395076383 : Nat.Prime 406039371947738395076383 := by
  apply lucas_primality 406039371947738395076383 (6 : ZMod 406039371947738395076383)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (856623147569068344043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (856623147569068344043, 1)] : List FactorBlock).map factorBlockValue).prod) = 406039371947738395076383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_79
      · exact prime_oneHundredThirtyNineEG_856623147569068344043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 406039371947738395076383) ^ 203019685973869197538191 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 406039371947738395076383) ^ 135346457315912798358794 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 406039371947738395076383) ^ 5139738885414410064258 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 406039371947738395076383) ^ 474 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_473367179847714661812293 : Nat.Prime 473367179847714661812293 := by
  apply lucas_primality 473367179847714661812293 (3 : ZMod 473367179847714661812293)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (110581, 1), (97289272085972903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (110581, 1), (97289272085972903, 1)] : List FactorBlock).map factorBlockValue).prod) = 473367179847714661812293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_110581
      · exact prime_oneHundredThirtyNineEG_97289272085972903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 473367179847714661812293) ^ 236683589923857330906146 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 473367179847714661812293) ^ 43033379986155878346572 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 473367179847714661812293) ^ 4280727971782807732 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 473367179847714661812293) ^ 4865564 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_923838123318655056548851 : Nat.Prime 923838123318655056548851 := by
  apply lucas_primality 923838123318655056548851 (2 : ZMod 923838123318655056548851)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (11, 1), (157411, 1), (894301, 1), (1325781293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (11, 1), (157411, 1), (894301, 1), (1325781293, 1)] : List FactorBlock).map factorBlockValue).prod) = 923838123318655056548851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_11
      · exact prime_oneHundredThirtyNineEG_157411
      · exact prime_oneHundredThirtyNineEG_894301
      · exact prime_oneHundredThirtyNineEG_1325781293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 923838123318655056548851) ^ 461919061659327528274425 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 923838123318655056548851) ^ 307946041106218352182950 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 923838123318655056548851) ^ 184767624663731011309770 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 923838123318655056548851) ^ 83985283938059550595350 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 923838123318655056548851) ^ 5868955303750405350 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 923838123318655056548851) ^ 1033028167606493850 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 923838123318655056548851) ^ 696825432819450 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1345222711565726800675163 : Nat.Prime 1345222711565726800675163 := by
  apply lucas_primality 1345222711565726800675163 (2 : ZMod 1345222711565726800675163)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (2130703, 1), (1960719201299107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (2130703, 1), (1960719201299107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1345222711565726800675163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_2130703
      · exact prime_oneHundredThirtyNineEG_1960719201299107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1345222711565726800675163) ^ 672611355782863400337581 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1345222711565726800675163) ^ 192174673080818114382166 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1345222711565726800675163) ^ 58487943981118556551094 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1345222711565726800675163) ^ 631351582818312454 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1345222711565726800675163) ^ 686086366 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_1374958976659072267604411 : Nat.Prime 1374958976659072267604411 := by
  apply lucas_primality 1374958976659072267604411 (2 : ZMod 1374958976659072267604411)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (67, 1), (1291902361, 1), (1588492783243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (67, 1), (1291902361, 1), (1588492783243, 1)] : List FactorBlock).map factorBlockValue).prod) = 1374958976659072267604411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_67
      · exact prime_oneHundredThirtyNineEG_1291902361
      · exact prime_oneHundredThirtyNineEG_1588492783243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1374958976659072267604411) ^ 687479488329536133802205 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1374958976659072267604411) ^ 274991795331814453520882 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1374958976659072267604411) ^ 20521775771030929367230 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1374958976659072267604411) ^ 1064290164772810 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1374958976659072267604411) ^ 865574581870 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2072922750486172754065861 : Nat.Prime 2072922750486172754065861 := by
  apply lucas_primality 2072922750486172754065861 (2 : ZMod 2072922750486172754065861)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (71, 1), (103, 1), (1999, 1), (139019133959089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (71, 1), (103, 1), (1999, 1), (139019133959089, 1)] : List FactorBlock).map factorBlockValue).prod) = 2072922750486172754065861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_17
      · exact prime_oneHundredThirtyNineEG_71
      · exact prime_oneHundredThirtyNineEG_103
      · exact prime_oneHundredThirtyNineEG_1999
      · exact prime_oneHundredThirtyNineEG_139019133959089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2072922750486172754065861) ^ 1036461375243086377032930 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072922750486172754065861) ^ 690974250162057584688620 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072922750486172754065861) ^ 414584550097234550813172 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072922750486172754065861) ^ 121936632381539573768580 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072922750486172754065861) ^ 29196095077270038789660 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072922750486172754065861) ^ 20125463596953133534620 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072922750486172754065861) ^ 1036979865175674214140 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072922750486172754065861) ^ 14911060740 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_2749917953318144535208823 : Nat.Prime 2749917953318144535208823 := by
  apply lucas_primality 2749917953318144535208823 (5 : ZMod 2749917953318144535208823)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1374958976659072267604411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1374958976659072267604411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2749917953318144535208823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_1374958976659072267604411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2749917953318144535208823) ^ 1374958976659072267604411 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 2749917953318144535208823) ^ 2 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4612397117244163951390139 : Nat.Prime 4612397117244163951390139 := by
  apply lucas_primality 4612397117244163951390139 (2 : ZMod 4612397117244163951390139)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (911, 1), (24859, 1), (79939, 1), (113809, 1), (11193331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (911, 1), (24859, 1), (79939, 1), (113809, 1), (11193331, 1)] : List FactorBlock).map factorBlockValue).prod) = 4612397117244163951390139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_911
      · exact prime_oneHundredThirtyNineEG_24859
      · exact prime_oneHundredThirtyNineEG_79939
      · exact prime_oneHundredThirtyNineEG_113809
      · exact prime_oneHundredThirtyNineEG_11193331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4612397117244163951390139) ^ 2306198558622081975695069 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4612397117244163951390139) ^ 5063004519477677224358 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4612397117244163951390139) ^ 185542343507146866382 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4612397117244163951390139) ^ 57698959422111409342 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4612397117244163951390139) ^ 40527525215441344282 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4612397117244163951390139) ^ 412066534728952798 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4900551586160085806169239 : Nat.Prime 4900551586160085806169239 := by
  apply lucas_primality 4900551586160085806169239 (11 : ZMod 4900551586160085806169239)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (9108831944535475476151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (9108831944535475476151, 1)] : List FactorBlock).map factorBlockValue).prod) = 4900551586160085806169239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_269
      · exact prime_oneHundredThirtyNineEG_9108831944535475476151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4900551586160085806169239) ^ 2450275793080042903084619 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 4900551586160085806169239) ^ 18217663889070950952302 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (11 : ZMod 4900551586160085806169239) ^ 538 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_14180265500931255278633123 : Nat.Prime 14180265500931255278633123 := by
  apply lucas_primality 14180265500931255278633123 (2 : ZMod 14180265500931255278633123)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (491, 1), (108572848880842038487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (491, 1), (108572848880842038487, 1)] : List FactorBlock).map factorBlockValue).prod) = 14180265500931255278633123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_19
      · exact prime_oneHundredThirtyNineEG_491
      · exact prime_oneHundredThirtyNineEG_108572848880842038487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14180265500931255278633123) ^ 7090132750465627639316561 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14180265500931255278633123) ^ 2025752214418750754090446 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14180265500931255278633123) ^ 746329763206908172559638 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14180265500931255278633123) ^ 28880377802303982237542 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14180265500931255278633123) ^ 130606 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_36229077797683491495608303 : Nat.Prime 36229077797683491495608303 := by
  apply lucas_primality 36229077797683491495608303 (5 : ZMod 36229077797683491495608303)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (53, 1), (967, 1), (1033, 1), (2226701, 1), (756949099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (53, 1), (967, 1), (1033, 1), (2226701, 1), (756949099, 1)] : List FactorBlock).map factorBlockValue).prod) = 36229077797683491495608303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_29
      · exact prime_oneHundredThirtyNineEG_53
      · exact prime_oneHundredThirtyNineEG_967
      · exact prime_oneHundredThirtyNineEG_1033
      · exact prime_oneHundredThirtyNineEG_2226701
      · exact prime_oneHundredThirtyNineEG_756949099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36229077797683491495608303) ^ 18114538898841745747804151 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36229077797683491495608303) ^ 5175582542526213070801186 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36229077797683491495608303) ^ 1249278544747706603296838 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36229077797683491495608303) ^ 683567505616669650860534 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36229077797683491495608303) ^ 37465437226146320057506 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36229077797683491495608303) ^ 35071711323991763306494 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36229077797683491495608303) ^ 16270293046836324902 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36229077797683491495608303) ^ 47861973606343498 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_45296333211216184516008617 : Nat.Prime 45296333211216184516008617 := by
  apply lucas_primality 45296333211216184516008617 (3 : ZMod 45296333211216184516008617)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (509, 1), (134033, 1), (6384107433948557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (509, 1), (134033, 1), (6384107433948557, 1)] : List FactorBlock).map factorBlockValue).prod) = 45296333211216184516008617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_13
      · exact prime_oneHundredThirtyNineEG_509
      · exact prime_oneHundredThirtyNineEG_134033
      · exact prime_oneHundredThirtyNineEG_6384107433948557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45296333211216184516008617) ^ 22648166605608092258004308 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45296333211216184516008617) ^ 3484333323939706501231432 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45296333211216184516008617) ^ 88990831456220401799624 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45296333211216184516008617) ^ 337949111123500813352 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 45296333211216184516008617) ^ 7095170888 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_61733695300635731564267191 : Nat.Prime 61733695300635731564267191 := by
  apply lucas_primality 61733695300635731564267191 (12 : ZMod 61733695300635731564267191)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (53, 1), (12942074486506442675947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (53, 1), (12942074486506442675947, 1)] : List FactorBlock).map factorBlockValue).prod) = 61733695300635731564267191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_53
      · exact prime_oneHundredThirtyNineEG_12942074486506442675947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 61733695300635731564267191) ^ 30866847650317865782133595 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (12 : ZMod 61733695300635731564267191) ^ 20577898433545243854755730 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (12 : ZMod 61733695300635731564267191) ^ 12346739060127146312853438 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (12 : ZMod 61733695300635731564267191) ^ 1164786703785579840835230 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (12 : ZMod 61733695300635731564267191) ^ 4770 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_88209928550881544511046303 : Nat.Prime 88209928550881544511046303 := by
  apply lucas_primality 88209928550881544511046303 (3 : ZMod 88209928550881544511046303)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4900551586160085806169239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4900551586160085806169239, 1)] : List FactorBlock).map factorBlockValue).prod) = 88209928550881544511046303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_4900551586160085806169239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 88209928550881544511046303) ^ 44104964275440772255523151 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 88209928550881544511046303) ^ 29403309516960514837015434 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 88209928550881544511046303) ^ 18 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_107619578841055872576345293 : Nat.Prime 107619578841055872576345293 := by
  apply lucas_primality 107619578841055872576345293 (2 : ZMod 107619578841055872576345293)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (137, 1), (1447, 1), (10908731, 1), (185691986941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (137, 1), (1447, 1), (10908731, 1), (185691986941, 1)] : List FactorBlock).map factorBlockValue).prod) = 107619578841055872576345293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_67
      · exact prime_oneHundredThirtyNineEG_137
      · exact prime_oneHundredThirtyNineEG_1447
      · exact prime_oneHundredThirtyNineEG_10908731
      · exact prime_oneHundredThirtyNineEG_185691986941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 107619578841055872576345293) ^ 53809789420527936288172646 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 107619578841055872576345293) ^ 1606262370762027948900676 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 107619578841055872576345293) ^ 785544371102597610046316 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 107619578841055872576345293) ^ 74374277015242482775636 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 107619578841055872576345293) ^ 9865453538184768932 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 107619578841055872576345293) ^ 579559627822012 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_161270948861915915038350601 : Nat.Prime 161270948861915915038350601 := by
  apply lucas_primality 161270948861915915038350601 (26 : ZMod 161270948861915915038350601)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (7, 2), (107, 1), (1467107, 1), (11647748618417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (7, 2), (107, 1), (1467107, 1), (11647748618417, 1)] : List FactorBlock).map factorBlockValue).prod) = 161270948861915915038350601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_7
      · exact prime_oneHundredThirtyNineEG_107
      · exact prime_oneHundredThirtyNineEG_1467107
      · exact prime_oneHundredThirtyNineEG_11647748618417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 161270948861915915038350601) ^ 80635474430957957519175300 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (26 : ZMod 161270948861915915038350601) ^ 53756982953971971679450200 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (26 : ZMod 161270948861915915038350601) ^ 32254189772383183007670120 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (26 : ZMod 161270948861915915038350601) ^ 23038706980273702148335800 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (26 : ZMod 161270948861915915038350601) ^ 1507205129550616028395800 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (26 : ZMod 161270948861915915038350601) ^ 109924462811448595800 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (26 : ZMod 161270948861915915038350601) ^ 13845675601800 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_540575976612803675737102837 : Nat.Prime 540575976612803675737102837 := by
  apply lucas_primality 540575976612803675737102837 (2 : ZMod 540575976612803675737102837)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (41, 1), (4889992279, 1), (9769124162999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (41, 1), (4889992279, 1), (9769124162999, 1)] : List FactorBlock).map factorBlockValue).prod) = 540575976612803675737102837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_23
      · exact prime_oneHundredThirtyNineEG_41
      · exact prime_oneHundredThirtyNineEG_4889992279
      · exact prime_oneHundredThirtyNineEG_9769124162999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 540575976612803675737102837) ^ 270287988306401837868551418 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 540575976612803675737102837) ^ 180191992204267891912367612 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 540575976612803675737102837) ^ 23503303330991464162482732 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 540575976612803675737102837) ^ 13184779917385455505782996 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 540575976612803675737102837) ^ 110547409028496684 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 540575976612803675737102837) ^ 55335152629164 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_4695288482579780497830836071 : Nat.Prime 4695288482579780497830836071 := by
  apply lucas_primality 4695288482579780497830836071 (3 : ZMod 4695288482579780497830836071)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (49303171, 1), (979648079, 1), (3240381041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (49303171, 1), (979648079, 1), (3240381041, 1)] : List FactorBlock).map factorBlockValue).prod) = 4695288482579780497830836071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_49303171
      · exact prime_oneHundredThirtyNineEG_979648079
      · exact prime_oneHundredThirtyNineEG_3240381041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4695288482579780497830836071) ^ 2347644241289890248915418035 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4695288482579780497830836071) ^ 1565096160859926832610278690 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4695288482579780497830836071) ^ 939057696515956099566167214 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4695288482579780497830836071) ^ 95232991861310107170 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4695288482579780497830836071) ^ 4792831817087430330 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4695288482579780497830836071) ^ 1448992702762755270 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_9129727605016239856893292361 : Nat.Prime 9129727605016239856893292361 := by
  apply lucas_primality 9129727605016239856893292361 (3 : ZMod 9129727605016239856893292361)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (83, 1), (2749917953318144535208823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (83, 1), (2749917953318144535208823, 1)] : List FactorBlock).map factorBlockValue).prod) = 9129727605016239856893292361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_83
      · exact prime_oneHundredThirtyNineEG_2749917953318144535208823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9129727605016239856893292361) ^ 4564863802508119928446646180 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9129727605016239856893292361) ^ 1825945521003247971378658472 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9129727605016239856893292361) ^ 109996718132725781408352920 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (3 : ZMod 9129727605016239856893292361) ^ 3320 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_23476442412898902489154180357 : Nat.Prime 23476442412898902489154180357 := by
  apply lucas_primality 23476442412898902489154180357 (2 : ZMod 23476442412898902489154180357)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (4297, 1), (6795335173359089613937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (4297, 1), (6795335173359089613937, 1)] : List FactorBlock).map factorBlockValue).prod) = 23476442412898902489154180357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_67
      · exact prime_oneHundredThirtyNineEG_4297
      · exact prime_oneHundredThirtyNineEG_6795335173359089613937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23476442412898902489154180357) ^ 11738221206449451244577090178 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23476442412898902489154180357) ^ 7825480804299634163051393452 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23476442412898902489154180357) ^ 350394662879088096853047468 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23476442412898902489154180357) ^ 5463449479380708049605348 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (2 : ZMod 23476442412898902489154180357) ^ 3454788 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_82167548445146158712039631241 : Nat.Prime 82167548445146158712039631241 := by
  apply lucas_primality 82167548445146158712039631241 (31 : ZMod 82167548445146158712039631241)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (83, 1), (2749917953318144535208823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (83, 1), (2749917953318144535208823, 1)] : List FactorBlock).map factorBlockValue).prod) = 82167548445146158712039631241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_5
      · exact prime_oneHundredThirtyNineEG_83
      · exact prime_oneHundredThirtyNineEG_2749917953318144535208823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 82167548445146158712039631241) ^ 41083774222573079356019815620 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (31 : ZMod 82167548445146158712039631241) ^ 27389182815048719570679877080 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (31 : ZMod 82167548445146158712039631241) ^ 16433509689029231742407926248 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (31 : ZMod 82167548445146158712039631241) ^ 989970463194532032675176280 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (31 : ZMod 82167548445146158712039631241) ^ 29880 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyNineEG_164335096890292317424079262439 : Nat.Prime 164335096890292317424079262439 := by
  apply lucas_primality 164335096890292317424079262439 (6 : ZMod 164335096890292317424079262439)
  · rw [← oneHundredThirtyNineEGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (873113, 1), (31369573944092825980921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (873113, 1), (31369573944092825980921, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyNineEG_2
      · exact prime_oneHundredThirtyNineEG_3
      · exact prime_oneHundredThirtyNineEG_873113
      · exact prime_oneHundredThirtyNineEG_31369573944092825980921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 164335096890292317424079262439) ^ 82167548445146158712039631219 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 164335096890292317424079262439) ^ 54778365630097439141359754146 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 164335096890292317424079262439) ^ 188217443664556955885526 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide
    · change (6 : ZMod 164335096890292317424079262439) ^ 5238678 ≠ 1
      rw [← oneHundredThirtyNineEGFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262400 : Nat.totient 164335096890292317424079262400 = 65260751149094586381038592000 := by
  rw [← show ((([(2, 6), (5, 2), (139, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_139, prime_oneHundredThirtyNineEG_171401, prime_oneHundredThirtyNineEG_714027719, prime_oneHundredThirtyNineEG_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262401 : Nat.totient 164335096890292317424079262401 = 140852363461608749038679030400 := by
  rw [← show ((([(7, 1), (22861, 1), (1087753, 1), (944075596789902971, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_22861, prime_oneHundredThirtyNineEG_1087753, prime_oneHundredThirtyNineEG_944075596789902971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262402 : Nat.totient 164335096890292317424079262402 = 54778154936436423842592558800 := by
  rw [← show ((([(2, 1), (3, 1), (259991, 1), (259143637967, 1), (406518401411, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_259991, prime_oneHundredThirtyNineEG_259143637967, prime_oneHundredThirtyNineEG_406518401411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262403 : Nat.totient 164335096890292317424079262403 = 163462992601215724567573522176 := by
  rw [← show ((([(223, 1), (2239, 1), (2633, 1), (78346927, 1), (1595506370789, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_223, prime_oneHundredThirtyNineEG_2239, prime_oneHundredThirtyNineEG_2633, prime_oneHundredThirtyNineEG_78346927, prime_oneHundredThirtyNineEG_1595506370789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262404 : Nat.totient 164335096890292317424079262404 = 82167548445136159018777420800 := by
  rw [← show ((([(2, 2), (8230555716241, 1), (4991616075388961, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_8230555716241, prime_oneHundredThirtyNineEG_4991616075388961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262405 : Nat.totient 164335096890292317424079262405 = 87641532951014797528963827456 := by
  rw [← show ((([(3, 1), (5, 1), (24623, 1), (299723, 1), (821515507, 1), (1807017109, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_24623, prime_oneHundredThirtyNineEG_299723, prime_oneHundredThirtyNineEG_821515507, prime_oneHundredThirtyNineEG_1807017109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262406 : Nat.totient 164335096890292317424079262406 = 77312639679105450688402910464 := by
  rw [← show ((([(2, 1), (17, 1), (3593, 1), (1345222711565726800675163, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_17, prime_oneHundredThirtyNineEG_3593, prime_oneHundredThirtyNineEG_1345222711565726800675163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262407 : Nat.totient 164335096890292317424079262407 = 164331185058026482655357645760 := by
  rw [← show ((([(42349, 1), (5244011, 1), (739986116310781513, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_42349, prime_oneHundredThirtyNineEG_5244011, prime_oneHundredThirtyNineEG_739986116310781513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262408 : Nat.totient 164335096890292317424079262408 = 46952884825797804978308359392 := by
  rw [← show ((([(2, 3), (3, 4), (7, 1), (36229077797683491495608303, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_36229077797683491495608303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262409 : Nat.totient 164335096890292317424079262409 = 144575446284031549832407876800 := by
  rw [← show ((([(11, 1), (31, 1), (166739, 1), (7939637, 1), (364030780417643, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_31, prime_oneHundredThirtyNineEG_166739, prime_oneHundredThirtyNineEG_7939637, prime_oneHundredThirtyNineEG_364030780417643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262410 : Nat.totient 164335096890292317424079262410 = 57483943602268085443691700480 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (19, 1), (775811, 1), (85758551877720999373, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_13, prime_oneHundredThirtyNineEG_19, prime_oneHundredThirtyNineEG_775811, prime_oneHundredThirtyNineEG_85758551877720999373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262411 : Nat.totient 164335096890292317424079262411 = 109341492102512766537566816672 := by
  rw [← show ((([(3, 1), (509, 1), (107619578841055872576345293, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_509, prime_oneHundredThirtyNineEG_107619578841055872576345293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262412 : Nat.totient 164335096890292317424079262412 = 82167548444403917378178735440 := by
  rw [← show ((([(2, 2), (110701963373, 1), (371120556228484511, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_110701963373, prime_oneHundredThirtyNineEG_371120556228484511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262413 : Nat.totient 164335096890292317424079262413 = 162881736338588556389030536320 := by
  rw [← show ((([(233, 1), (331, 1), (643, 1), (3313869771241836598117, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_233, prime_oneHundredThirtyNineEG_331, prime_oneHundredThirtyNineEG_643, prime_oneHundredThirtyNineEG_3313869771241836598117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262414 : Nat.totient 164335096890292317424079262414 = 53611038510928350478059953280 := by
  rw [← show ((([(2, 1), (3, 1), (47, 1), (29297, 1), (19891066338975030898291, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_47, prime_oneHundredThirtyNineEG_29297, prime_oneHundredThirtyNineEG_19891066338975030898291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262415 : Nat.totient 164335096890292317424079262415 = 111525181554991964608366193664 := by
  rw [← show ((([(5, 1), (7, 1), (97, 1), (5269259, 1), (9186307961495977903, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_97, prime_oneHundredThirtyNineEG_5269259, prime_oneHundredThirtyNineEG_9186307961495977903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262416 : Nat.totient 164335096890292317424079262416 = 82167548445109108605365300736 := by
  rw [← show ((([(2, 4), (2218804223837, 1), (4629044530067473, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_2218804223837, prime_oneHundredThirtyNineEG_4629044530067473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262417 : Nat.totient 164335096890292317424079262417 = 109556730617763763496261423328 := by
  rw [← show ((([(3, 2), (170534597, 1), (107071852464239146229, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_170534597, prime_oneHundredThirtyNineEG_107071852464239146229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262418 : Nat.totient 164335096890292317424079262418 = 80122702325217643018700365824 := by
  rw [← show ((([(2, 1), (43, 1), (929, 1), (1777, 1), (32479, 1), (35639047048343509, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_43, prime_oneHundredThirtyNineEG_929, prime_oneHundredThirtyNineEG_1777, prime_oneHundredThirtyNineEG_32479, prime_oneHundredThirtyNineEG_35639047048343509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262419 : Nat.totient 164335096890292317424079262419 = 164173825941430401509040910800 := by
  rw [← show ((([(1019, 1), (161270948861915915038350601, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_1019, prime_oneHundredThirtyNineEG_161270948861915915038350601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262420 : Nat.totient 164335096890292317424079262420 = 38106689111068958801412794880 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (1663186003, 1), (6509051867313773, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_23, prime_oneHundredThirtyNineEG_1663186003, prime_oneHundredThirtyNineEG_6509051867313773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262421 : Nat.totient 164335096890292317424079262421 = 163324021038144030678315564720 := by
  rw [← show ((([(163, 1), (56611, 1), (17809096791578509956397, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_163, prime_oneHundredThirtyNineEG_56611, prime_oneHundredThirtyNineEG_17809096791578509956397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262422 : Nat.totient 164335096890292317424079262422 = 70175019149587028923063070400 := by
  rw [← show ((([(2, 1), (7, 1), (311, 1), (2521, 1), (14971628936163813987683, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_311, prime_oneHundredThirtyNineEG_2521, prime_oneHundredThirtyNineEG_14971628936163813987683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262423 : Nat.totient 164335096890292317424079262423 = 95180503421278001402518118400 := by
  rw [← show ((([(3, 1), (13, 1), (17, 1), (19810801, 1), (251483923, 1), (49751311627, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_13, prime_oneHundredThirtyNineEG_17, prime_oneHundredThirtyNineEG_19810801, prime_oneHundredThirtyNineEG_251483923, prime_oneHundredThirtyNineEG_49751311627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262424 : Nat.totient 164335096890292317424079262424 = 81969138643386989675342188800 := by
  rw [← show ((([(2, 3), (443, 1), (6343, 1), (15767497, 1), (463638127907551, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_443, prime_oneHundredThirtyNineEG_6343, prime_oneHundredThirtyNineEG_15767497, prime_oneHundredThirtyNineEG_463638127907551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262425 : Nat.totient 164335096890292317424079262425 = 125037990965912498513061200640 := by
  rw [← show ((([(5, 2), (29, 1), (67, 1), (57973, 1), (58356836509590770923, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_29, prime_oneHundredThirtyNineEG_67, prime_oneHundredThirtyNineEG_57973, prime_oneHundredThirtyNineEG_58356836509590770923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262426 : Nat.totient 164335096890292317424079262426 = 54695193816355624216788989760 := by
  rw [← show ((([(2, 1), (3, 2), (659, 1), (1131343, 1), (12245544798078052361, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_659, prime_oneHundredThirtyNineEG_1131343, prime_oneHundredThirtyNineEG_12245544798078052361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262427 : Nat.totient 164335096890292317424079262427 = 162739604829731723076629580840 := by
  rw [← show ((([(103, 1), (28636291, 1), (55715538635071614799, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_103, prime_oneHundredThirtyNineEG_28636291, prime_oneHundredThirtyNineEG_55715538635071614799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262428 : Nat.totient 164335096890292317424079262428 = 81802780362959961735369904640 := by
  rw [← show ((([(2, 2), (293, 1), (971, 1), (144405416542437441278369, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_293, prime_oneHundredThirtyNineEG_971, prime_oneHundredThirtyNineEG_144405416542437441278369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262429 : Nat.totient 164335096890292317424079262429 = 88960177154368747419222675456 := by
  rw [← show ((([(3, 1), (7, 2), (19, 2), (27953, 1), (92377367, 1), (1199255681137, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_19, prime_oneHundredThirtyNineEG_27953, prime_oneHundredThirtyNineEG_92377367, prime_oneHundredThirtyNineEG_1199255681137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262430 : Nat.totient 164335096890292317424079262430 = 64493773482190761218627360256 := by
  rw [← show ((([(2, 1), (5, 1), (53, 1), (164636113, 1), (1883342693760762887, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_53, prime_oneHundredThirtyNineEG_164636113, prime_oneHundredThirtyNineEG_1883342693760762887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262431 : Nat.totient 164335096890292317424079262431 = 143906790058017915283372305600 := by
  rw [← show ((([(11, 1), (41, 1), (79, 1), (4612397117244163951390139, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_41, prime_oneHundredThirtyNineEG_79, prime_oneHundredThirtyNineEG_4612397117244163951390139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262432 : Nat.totient 164335096890292317424079262432 = 54778365282830329743715865600 := by
  rw [← show ((([(2, 5), (3, 1), (157741301, 1), (10852097168518630217, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_157741301, prime_oneHundredThirtyNineEG_10852097168518630217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262433 : Nat.totient 164335096890292317424079262433 = 164334173052168998769022535700 := by
  rw [← show ((([(177883, 1), (923838123318655056548851, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_177883, prime_oneHundredThirtyNineEG_923838123318655056548851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262434 : Nat.totient 164335096890292317424079262434 = 79905402107508318300155079360 := by
  rw [← show ((([(2, 1), (37, 1), (1931, 1), (3582476957, 1), (321020617690723, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_37, prime_oneHundredThirtyNineEG_1931, prime_oneHundredThirtyNineEG_3582476957, prime_oneHundredThirtyNineEG_321020617690723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262435 : Nat.totient 164335096890292317424079262435 = 85872995344101624220001894400 := by
  rw [← show ((([(3, 3), (5, 1), (61, 1), (257, 1), (712007, 1), (4897219, 1), (22268953541, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_61, prime_oneHundredThirtyNineEG_257, prime_oneHundredThirtyNineEG_712007, prime_oneHundredThirtyNineEG_4897219, prime_oneHundredThirtyNineEG_22268953541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262436 : Nat.totient 164335096890292317424079262436 = 64895765196075114184565096448 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (769, 1), (2069, 1), (283754077563275054159, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_13, prime_oneHundredThirtyNineEG_769, prime_oneHundredThirtyNineEG_2069, prime_oneHundredThirtyNineEG_283754077563275054159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262437 : Nat.totient 164335096890292317424079262437 = 161549752956093106100646379632 := by
  rw [← show ((([(59, 1), (61060123, 1), (243912283, 1), (187019532727, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_59, prime_oneHundredThirtyNineEG_61060123, prime_oneHundredThirtyNineEG_243912283, prime_oneHundredThirtyNineEG_187019532727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262438 : Nat.totient 164335096890292317424079262438 = 54778302890949550955706046080 := by
  rw [← show ((([(2, 1), (3, 1), (873113, 1), (31369573944092825980921, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_873113, prime_oneHundredThirtyNineEG_31369573944092825980921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262439 : Nat.totient 164335096890292317424079262439 = 164335096890292317424079262438 := by
  rw [← show ((([(164335096890292317424079262439, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_164335096890292317424079262439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262440 : Nat.totient 164335096890292317424079262440 = 59871538804624634617312112640 := by
  rw [← show ((([(2, 3), (5, 1), (17, 1), (31, 1), (837979, 1), (9303076312089536917, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_17, prime_oneHundredThirtyNineEG_31, prime_oneHundredThirtyNineEG_837979, prime_oneHundredThirtyNineEG_9303076312089536917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262441 : Nat.totient 164335096890292317424079262441 = 109555919181450982805929085712 := by
  rw [← show ((([(3, 1), (134909, 1), (406039371947738395076383, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_134909, prime_oneHundredThirtyNineEG_406039371947738395076383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262442 : Nat.totient 164335096890292317424079262442 = 74697771313769235192763299900 := by
  rw [← show ((([(2, 1), (11, 3), (61733695300635731564267191, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_61733695300635731564267191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262443 : Nat.totient 164335096890292317424079262443 = 134734365119798170454301668160 := by
  rw [← show ((([(7, 1), (23, 1), (4146797843, 1), (246145321320729641, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_23, prime_oneHundredThirtyNineEG_4146797843, prime_oneHundredThirtyNineEG_246145321320729641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262444 : Nat.totient 164335096890292317424079262444 = 54778349412537113332102049280 := by
  rw [← show ((([(2, 2), (3, 2), (3436757, 1), (196632391, 1), (6754977991217, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_3436757, prime_oneHundredThirtyNineEG_196632391, prime_oneHundredThirtyNineEG_6754977991217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262445 : Nat.totient 164335096890292317424079262445 = 131467864346451925651934594880 := by
  rw [← show ((([(5, 1), (616741, 1), (53291445482071831587029, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_616741, prime_oneHundredThirtyNineEG_53291445482071831587029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262446 : Nat.totient 164335096890292317424079262446 = 82051656202736677474687852800 := by
  rw [← show ((([(2, 1), (709, 1), (1131291947, 1), (102442318437469601, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_709, prime_oneHundredThirtyNineEG_1131291947, prime_oneHundredThirtyNineEG_102442318437469601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262447 : Nat.totient 164335096890292317424079262447 = 109528370729193015772162234328 := by
  rw [← show ((([(3, 1), (3863, 1), (14180265500931255278633123, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_3863, prime_oneHundredThirtyNineEG_14180265500931255278633123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262448 : Nat.totient 164335096890292317424079262448 = 77842940632243729306142808384 := by
  rw [← show ((([(2, 4), (19, 1), (540575976612803675737102837, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_19, prime_oneHundredThirtyNineEG_540575976612803675737102837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262449 : Nat.totient 164335096890292317424079262449 = 151693935590555873060303040192 := by
  rw [← show ((([(13, 2), (313974983797, 1), (3097052546225093, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_13, prime_oneHundredThirtyNineEG_313974983797, prime_oneHundredThirtyNineEG_3097052546225093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262450 : Nat.totient 164335096890292317424079262450 = 37562307048839713958004096000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (7, 1), (49303171, 1), (979648079, 1), (3240381041, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_49303171, prime_oneHundredThirtyNineEG_979648079, prime_oneHundredThirtyNineEG_3240381041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262451 : Nat.totient 164335096890292317424079262451 = 163582630239917540345871038400 := by
  rw [← show ((([(281, 1), (991, 1), (67967, 1), (8682649099776818443, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_281, prime_oneHundredThirtyNineEG_991, prime_oneHundredThirtyNineEG_67967, prime_oneHundredThirtyNineEG_8682649099776818443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262452 : Nat.totient 164335096890292317424079262452 = 82167498809208476190218152160 := by
  rw [← show ((([(2, 2), (2052317, 1), (8559599, 1), (2338688994747311, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_2052317, prime_oneHundredThirtyNineEG_8559599, prime_oneHundredThirtyNineEG_2338688994747311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262453 : Nat.totient 164335096890292317424079262453 = 99229437239148449777409588000 := by
  rw [← show ((([(3, 2), (11, 1), (271, 1), (1332491, 1), (4596862943550149627, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_271, prime_oneHundredThirtyNineEG_1332491, prime_oneHundredThirtyNineEG_4596862943550149627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262454 : Nat.totient 164335096890292317424079262454 = 79323479782610774336256627360 := by
  rw [← show ((([(2, 1), (29, 1), (7411, 1), (382318680270921410913133, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_29, prime_oneHundredThirtyNineEG_7411, prime_oneHundredThirtyNineEG_382318680270921410913133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262455 : Nat.totient 164335096890292317424079262455 = 130228928330271785906442485760 := by
  rw [← show ((([(5, 1), (113, 1), (1721, 1), (347962513, 1), (485700497565859, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_113, prime_oneHundredThirtyNineEG_1721, prime_oneHundredThirtyNineEG_347962513, prime_oneHundredThirtyNineEG_485700497565859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262456 : Nat.totient 164335096890292317424079262456 = 53259058641131779500194457600 := by
  rw [← show ((([(2, 3), (3, 1), (71, 1), (73, 1), (6691, 1), (197445320252374796473, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_71, prime_oneHundredThirtyNineEG_73, prime_oneHundredThirtyNineEG_6691, prime_oneHundredThirtyNineEG_197445320252374796473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262457 : Nat.totient 164335096890292317424079262457 = 132300417460114796054893430784 := by
  rw [← show ((([(7, 1), (17, 1), (653, 1), (1907, 1), (1108969212933376726793, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_17, prime_oneHundredThirtyNineEG_653, prime_oneHundredThirtyNineEG_1907, prime_oneHundredThirtyNineEG_1108969212933376726793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262458 : Nat.totient 164335096890292317424079262458 = 82137254130636108121402196256 := by
  rw [← show ((([(2, 1), (2713, 1), (10648459, 1), (2844223842622615087, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_2713, prime_oneHundredThirtyNineEG_10648459, prime_oneHundredThirtyNineEG_2844223842622615087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262459 : Nat.totient 164335096890292317424079262459 = 109539442835500133885000394240 := by
  rw [← show ((([(3, 1), (6337, 1), (43311587491, 1), (199581949849859, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_6337, prime_oneHundredThirtyNineEG_43311587491, prime_oneHundredThirtyNineEG_199581949849859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262460 : Nat.totient 164335096890292317424079262460 = 65104949266183762439707929600 := by
  rw [← show ((([(2, 2), (5, 1), (151, 1), (337, 1), (161470608299066871130229, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_151, prime_oneHundredThirtyNineEG_337, prime_oneHundredThirtyNineEG_161470608299066871130229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262461 : Nat.totient 164335096890292317424079262461 = 157096178636492716466077552320 := by
  rw [← show ((([(43, 1), (47, 1), (78781, 1), (4889666627, 1), (211087867343, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_43, prime_oneHundredThirtyNineEG_47, prime_oneHundredThirtyNineEG_78781, prime_oneHundredThirtyNineEG_4889666627, prime_oneHundredThirtyNineEG_211087867343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262462 : Nat.totient 164335096890292317424079262462 = 50564644978180585050694770912 := by
  rw [← show ((([(2, 1), (3, 3), (13, 1), (231065587, 1), (1013113127987340763, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_13, prime_oneHundredThirtyNineEG_231065587, prime_oneHundredThirtyNineEG_1013113127987340763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262463 : Nat.totient 164335096890292317424079262463 = 164053955317524500911951097856 := by
  rw [← show ((([(593, 1), (40849, 1), (395481607, 1), (17154099007337, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_593, prime_oneHundredThirtyNineEG_40849, prime_oneHundredThirtyNineEG_395481607, prime_oneHundredThirtyNineEG_17154099007337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262464 : Nat.totient 164335096890292317424079262464 = 64024176770278463290645463040 := by
  rw [← show ((([(2, 8), (7, 1), (11, 1), (26987, 1), (864427, 1), (1708037, 1), (209227819, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_26987, prime_oneHundredThirtyNineEG_864427, prime_oneHundredThirtyNineEG_1708037, prime_oneHundredThirtyNineEG_209227819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262465 : Nat.totient 164335096890292317424079262465 = 87639634808075553736120433664 := by
  rw [← show ((([(3, 1), (5, 1), (20147, 1), (62869, 1), (14906933, 1), (580234873949, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_20147, prime_oneHundredThirtyNineEG_62869, prime_oneHundredThirtyNineEG_14906933, prime_oneHundredThirtyNineEG_580234873949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262466 : Nat.totient 164335096890292317424079262466 = 78584632260878806436782219504 := by
  rw [← show ((([(2, 1), (23, 1), (7547, 1), (473367179847714661812293, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_23, prime_oneHundredThirtyNineEG_7547, prime_oneHundredThirtyNineEG_473367179847714661812293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262467 : Nat.totient 164335096890292317424079262467 = 154879217305945501605795717120 := by
  rw [← show ((([(19, 1), (193, 2), (113771641, 1), (2040929880151577, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_19, prime_oneHundredThirtyNineEG_193, prime_oneHundredThirtyNineEG_113771641, prime_oneHundredThirtyNineEG_2040929880151577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262468 : Nat.totient 164335096890292317424079262468 = 54518752518069303085250764800 := by
  rw [← show ((([(2, 2), (3, 1), (211, 1), (11414002441, 1), (5686285520649089, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_211, prime_oneHundredThirtyNineEG_11414002441, prime_oneHundredThirtyNineEG_5686285520649089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262469 : Nat.totient 164335096890292317424079262469 = 164324703484874839607369828208 := by
  rw [← show ((([(18803, 1), (99623, 1), (40183867, 1), (2183191519603, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_18803, prime_oneHundredThirtyNineEG_99623, prime_oneHundredThirtyNineEG_40183867, prime_oneHundredThirtyNineEG_2183191519603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262470 : Nat.totient 164335096890292317424079262470 = 65112801571817696112128563200 := by
  rw [← show ((([(2, 1), (5, 1), (107, 1), (9467, 1), (2990401, 1), (5425062440651663, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_107, prime_oneHundredThirtyNineEG_9467, prime_oneHundredThirtyNineEG_2990401, prime_oneHundredThirtyNineEG_5425062440651663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262471 : Nat.totient 164335096890292317424079262471 = 88304545230838988089682534400 := by
  rw [← show ((([(3, 2), (7, 1), (31, 1), (37, 1), (997, 1), (3877, 1), (20011, 1), (29401304947129, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_31, prime_oneHundredThirtyNineEG_37, prime_oneHundredThirtyNineEG_997, prime_oneHundredThirtyNineEG_3877, prime_oneHundredThirtyNineEG_20011, prime_oneHundredThirtyNineEG_29401304947129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262472 : Nat.totient 164335096890292317424079262472 = 79420513382486263197450240000 := by
  rw [← show ((([(2, 3), (41, 1), (131, 1), (617, 1), (38329, 1), (9049553, 1), (17870858051, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_41, prime_oneHundredThirtyNineEG_131, prime_oneHundredThirtyNineEG_617, prime_oneHundredThirtyNineEG_38329, prime_oneHundredThirtyNineEG_9049553, prime_oneHundredThirtyNineEG_17870858051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262473 : Nat.totient 164335096890292317424079262473 = 162488635127444785598408881120 := by
  rw [← show ((([(89, 1), (4662745489427, 1), (396003120264491, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_89, prime_oneHundredThirtyNineEG_4662745489427, prime_oneHundredThirtyNineEG_396003120264491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262474 : Nat.totient 164335096890292317424079262474 = 51555706910674999575008256000 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (129347, 1), (15481901, 1), (804543456589921, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_17, prime_oneHundredThirtyNineEG_129347, prime_oneHundredThirtyNineEG_15481901, prime_oneHundredThirtyNineEG_804543456589921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262475 : Nat.totient 164335096890292317424079262475 = 110304990409012042723345152000 := by
  rw [← show ((([(5, 2), (11, 1), (13, 1), (6173, 1), (7446599590152573633841, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_13, prime_oneHundredThirtyNineEG_6173, prime_oneHundredThirtyNineEG_7446599590152573633841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262476 : Nat.totient 164335096890292317424079262476 = 82076955778723726343007612192 := by
  rw [← show ((([(2, 2), (907, 1), (45296333211216184516008617, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_907, prime_oneHundredThirtyNineEG_45296333211216184516008617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262477 : Nat.totient 164335096890292317424079262477 = 109034420671203766815757560000 := by
  rw [← show ((([(3, 1), (251, 1), (1453, 1), (10163, 1), (14779093922424189131, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_251, prime_oneHundredThirtyNineEG_1453, prime_oneHundredThirtyNineEG_10163, prime_oneHundredThirtyNineEG_14779093922424189131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262478 : Nat.totient 164335096890292317424079262478 = 70372388465886694928534841600 := by
  rw [← show ((([(2, 1), (7, 2), (1787, 1), (8389, 1), (9323, 1), (44351, 1), (270526866349, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_1787, prime_oneHundredThirtyNineEG_8389, prime_oneHundredThirtyNineEG_9323, prime_oneHundredThirtyNineEG_44351, prime_oneHundredThirtyNineEG_270526866349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262479 : Nat.totient 164335096890292317424079262479 = 162705227618090189000013817600 := by
  rw [← show ((([(101, 1), (58337, 1), (27891049715114198608067, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_101, prime_oneHundredThirtyNineEG_58337, prime_oneHundredThirtyNineEG_27891049715114198608067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262480 : Nat.totient 164335096890292317424079262480 = 43294708257040867562327693568 := by
  rw [← show ((([(2, 4), (3, 2), (5, 1), (83, 1), (2749917953318144535208823, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_83, prime_oneHundredThirtyNineEG_2749917953318144535208823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262481 : Nat.totient 164335096890292317424079262481 = 164335093936203791202572204032 := by
  rw [← show ((([(55629713, 1), (2954088526221451428737, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_55629713, prime_oneHundredThirtyNineEG_2954088526221451428737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262482 : Nat.totient 164335096890292317424079262482 = 82167548445146158712039631240 := by
  rw [← show ((([(2, 1), (82167548445146158712039631241, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_82167548445146158712039631241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262483 : Nat.totient 164335096890292317424079262483 = 103782916003539760648753397760 := by
  rw [← show ((([(3, 1), (29, 2), (53, 1), (616321, 1), (1994023348740590117, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_29, prime_oneHundredThirtyNineEG_53, prime_oneHundredThirtyNineEG_616321, prime_oneHundredThirtyNineEG_1994023348740590117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262484 : Nat.totient 164335096890292317424079262484 = 82080229009027151830387992960 := by
  rw [← show ((([(2, 2), (941, 1), (1886471557, 1), (23143575180095333, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_941, prime_oneHundredThirtyNineEG_1886471557, prime_oneHundredThirtyNineEG_23143575180095333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262485 : Nat.totient 164335096890292317424079262485 = 112686923581914731947940065680 := by
  rw [← show ((([(5, 1), (7, 1), (4695288482579780497830836071, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_4695288482579780497830836071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262486 : Nat.totient 164335096890292317424079262486 = 46892015905587508790825961600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (19, 1), (167, 1), (15511, 1), (160385999, 1), (315435135143, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_19, prime_oneHundredThirtyNineEG_167, prime_oneHundredThirtyNineEG_15511, prime_oneHundredThirtyNineEG_160385999, prime_oneHundredThirtyNineEG_315435135143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262487 : Nat.totient 164335096890292317424079262487 = 163041119749156573674982374912 := by
  rw [← show ((([(127, 1), (610130334497, 1), (2120820860243273, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_127, prime_oneHundredThirtyNineEG_610130334497, prime_oneHundredThirtyNineEG_2120820860243273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262488 : Nat.totient 164335096890292317424079262488 = 75846967795437053160188396160 := by
  rw [← show ((([(2, 3), (13, 1), (920095558957, 1), (1717370708970571, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_13, prime_oneHundredThirtyNineEG_920095558957, prime_oneHundredThirtyNineEG_1717370708970571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262489 : Nat.totient 164335096890292317424079262489 = 104793395118447274879123006776 := by
  rw [← show ((([(3, 4), (23, 1), (88209928550881544511046303, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_23, prime_oneHundredThirtyNineEG_88209928550881544511046303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262490 : Nat.totient 164335096890292317424079262490 = 65733979967221866599630559744 := by
  rw [← show ((([(2, 1), (5, 1), (1118137, 1), (14697223765092499168177, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_1118137, prime_oneHundredThirtyNineEG_14697223765092499168177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262491 : Nat.totient 164335096890292317424079262491 = 154666905756956019167780497920 := by
  rw [← show ((([(17, 1), (110419, 1), (7738037, 1), (11313755581287941, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_17, prime_oneHundredThirtyNineEG_110419, prime_oneHundredThirtyNineEG_7738037, prime_oneHundredThirtyNineEG_11313755581287941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262492 : Nat.totient 164335096890292317424079262492 = 46241331689125027986646984704 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (67, 1), (4297, 1), (6795335173359089613937, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_67, prime_oneHundredThirtyNineEG_4297, prime_oneHundredThirtyNineEG_6795335173359089613937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262493 : Nat.totient 164335096890292317424079262493 = 164234091913658527335893860416 := by
  rw [← show ((([(1627, 1), (3161468725847, 1), (31948750829297, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_1627, prime_oneHundredThirtyNineEG_3161468725847, prime_oneHundredThirtyNineEG_31948750829297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262494 : Nat.totient 164335096890292317424079262494 = 82146874301044163071604720640 := by
  rw [← show ((([(2, 1), (4019, 1), (363017, 1), (26673949, 1), (2111387973361, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_4019, prime_oneHundredThirtyNineEG_363017, prime_oneHundredThirtyNineEG_26673949, prime_oneHundredThirtyNineEG_2111387973361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262495 : Nat.totient 164335096890292317424079262495 = 87638477812055206883425812480 := by
  rw [← show ((([(3, 1), (5, 1), (12689, 1), (42349041521, 1), (20387692905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_12689, prime_oneHundredThirtyNineEG_42349041521, prime_oneHundredThirtyNineEG_20387692905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262496 : Nat.totient 164335096890292317424079262496 = 79450688567445573693455078400 := by
  rw [← show ((([(2, 5), (59, 1), (61, 1), (10739543, 1), (20773331, 1), (6395972059, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_59, prime_oneHundredThirtyNineEG_61, prime_oneHundredThirtyNineEG_10739543, prime_oneHundredThirtyNineEG_20773331, prime_oneHundredThirtyNineEG_6395972059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262497 : Nat.totient 164335096890292317424079262497 = 149374813400033608657985871600 := by
  rw [← show ((([(11, 1), (7207, 1), (2072922750486172754065861, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_11, prime_oneHundredThirtyNineEG_7207, prime_oneHundredThirtyNineEG_2072922750486172754065861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262498 : Nat.totient 164335096890292317424079262498 = 54778365630097439141359754160 := by
  rw [← show ((([(2, 1), (3, 2), (9129727605016239856893292361, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_9129727605016239856893292361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262499 : Nat.totient 164335096890292317424079262499 = 140858654477393414934925082136 := by
  rw [← show ((([(7, 1), (23476442412898902489154180357, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_7, prime_oneHundredThirtyNineEG_23476442412898902489154180357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262500 : Nat.totient 164335096890292317424079262500 = 65354073213666001433592000000 := by
  rw [← show ((([(2, 2), (5, 5), (173, 1), (189285081917, 1), (401474366701, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_2, prime_oneHundredThirtyNineEG_5, prime_oneHundredThirtyNineEG_173, prime_oneHundredThirtyNineEG_189285081917, prime_oneHundredThirtyNineEG_401474366701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyNineEG_164335096890292317424079262501 : Nat.totient 164335096890292317424079262501 = 101129290386154659071524415040 := by
  rw [← show ((([(3, 1), (13, 1), (12847717079, 1), (327974254661310821, 1)] : List FactorBlock).map factorBlockValue).prod) = 164335096890292317424079262501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyNineEG_3, prime_oneHundredThirtyNineEG_13, prime_oneHundredThirtyNineEG_12847717079, prime_oneHundredThirtyNineEG_327974254661310821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtyNineEG : certifiedKill 1 164335096890292317424079262399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtyNineEG_164335096890292317424079262400, phi_oneHundredThirtyNineEG_164335096890292317424079262401, phi_oneHundredThirtyNineEG_164335096890292317424079262402,
    phi_oneHundredThirtyNineEG_164335096890292317424079262403, phi_oneHundredThirtyNineEG_164335096890292317424079262404, phi_oneHundredThirtyNineEG_164335096890292317424079262405,
    phi_oneHundredThirtyNineEG_164335096890292317424079262406, phi_oneHundredThirtyNineEG_164335096890292317424079262407, phi_oneHundredThirtyNineEG_164335096890292317424079262408,
    phi_oneHundredThirtyNineEG_164335096890292317424079262409, phi_oneHundredThirtyNineEG_164335096890292317424079262410, phi_oneHundredThirtyNineEG_164335096890292317424079262411,
    phi_oneHundredThirtyNineEG_164335096890292317424079262412, phi_oneHundredThirtyNineEG_164335096890292317424079262413, phi_oneHundredThirtyNineEG_164335096890292317424079262414,
    phi_oneHundredThirtyNineEG_164335096890292317424079262415, phi_oneHundredThirtyNineEG_164335096890292317424079262416, phi_oneHundredThirtyNineEG_164335096890292317424079262417,
    phi_oneHundredThirtyNineEG_164335096890292317424079262418, phi_oneHundredThirtyNineEG_164335096890292317424079262419, phi_oneHundredThirtyNineEG_164335096890292317424079262420,
    phi_oneHundredThirtyNineEG_164335096890292317424079262421, phi_oneHundredThirtyNineEG_164335096890292317424079262422, phi_oneHundredThirtyNineEG_164335096890292317424079262423,
    phi_oneHundredThirtyNineEG_164335096890292317424079262424, phi_oneHundredThirtyNineEG_164335096890292317424079262425, phi_oneHundredThirtyNineEG_164335096890292317424079262426,
    phi_oneHundredThirtyNineEG_164335096890292317424079262427, phi_oneHundredThirtyNineEG_164335096890292317424079262428, phi_oneHundredThirtyNineEG_164335096890292317424079262429,
    phi_oneHundredThirtyNineEG_164335096890292317424079262430, phi_oneHundredThirtyNineEG_164335096890292317424079262431, phi_oneHundredThirtyNineEG_164335096890292317424079262432,
    phi_oneHundredThirtyNineEG_164335096890292317424079262433, phi_oneHundredThirtyNineEG_164335096890292317424079262434, phi_oneHundredThirtyNineEG_164335096890292317424079262435,
    phi_oneHundredThirtyNineEG_164335096890292317424079262436, phi_oneHundredThirtyNineEG_164335096890292317424079262437, phi_oneHundredThirtyNineEG_164335096890292317424079262438,
    phi_oneHundredThirtyNineEG_164335096890292317424079262439, phi_oneHundredThirtyNineEG_164335096890292317424079262440, phi_oneHundredThirtyNineEG_164335096890292317424079262441,
    phi_oneHundredThirtyNineEG_164335096890292317424079262442, phi_oneHundredThirtyNineEG_164335096890292317424079262443, phi_oneHundredThirtyNineEG_164335096890292317424079262444,
    phi_oneHundredThirtyNineEG_164335096890292317424079262445, phi_oneHundredThirtyNineEG_164335096890292317424079262446, phi_oneHundredThirtyNineEG_164335096890292317424079262447,
    phi_oneHundredThirtyNineEG_164335096890292317424079262448, phi_oneHundredThirtyNineEG_164335096890292317424079262449, phi_oneHundredThirtyNineEG_164335096890292317424079262450,
    phi_oneHundredThirtyNineEG_164335096890292317424079262451, phi_oneHundredThirtyNineEG_164335096890292317424079262452, phi_oneHundredThirtyNineEG_164335096890292317424079262453,
    phi_oneHundredThirtyNineEG_164335096890292317424079262454, phi_oneHundredThirtyNineEG_164335096890292317424079262455, phi_oneHundredThirtyNineEG_164335096890292317424079262456,
    phi_oneHundredThirtyNineEG_164335096890292317424079262457, phi_oneHundredThirtyNineEG_164335096890292317424079262458, phi_oneHundredThirtyNineEG_164335096890292317424079262459,
    phi_oneHundredThirtyNineEG_164335096890292317424079262460, phi_oneHundredThirtyNineEG_164335096890292317424079262461, phi_oneHundredThirtyNineEG_164335096890292317424079262462,
    phi_oneHundredThirtyNineEG_164335096890292317424079262463, phi_oneHundredThirtyNineEG_164335096890292317424079262464, phi_oneHundredThirtyNineEG_164335096890292317424079262465,
    phi_oneHundredThirtyNineEG_164335096890292317424079262466, phi_oneHundredThirtyNineEG_164335096890292317424079262467, phi_oneHundredThirtyNineEG_164335096890292317424079262468,
    phi_oneHundredThirtyNineEG_164335096890292317424079262469, phi_oneHundredThirtyNineEG_164335096890292317424079262470, phi_oneHundredThirtyNineEG_164335096890292317424079262471,
    phi_oneHundredThirtyNineEG_164335096890292317424079262472, phi_oneHundredThirtyNineEG_164335096890292317424079262473, phi_oneHundredThirtyNineEG_164335096890292317424079262474,
    phi_oneHundredThirtyNineEG_164335096890292317424079262475, phi_oneHundredThirtyNineEG_164335096890292317424079262476, phi_oneHundredThirtyNineEG_164335096890292317424079262477,
    phi_oneHundredThirtyNineEG_164335096890292317424079262478, phi_oneHundredThirtyNineEG_164335096890292317424079262479, phi_oneHundredThirtyNineEG_164335096890292317424079262480,
    phi_oneHundredThirtyNineEG_164335096890292317424079262481, phi_oneHundredThirtyNineEG_164335096890292317424079262482, phi_oneHundredThirtyNineEG_164335096890292317424079262483,
    phi_oneHundredThirtyNineEG_164335096890292317424079262484, phi_oneHundredThirtyNineEG_164335096890292317424079262485, phi_oneHundredThirtyNineEG_164335096890292317424079262486,
    phi_oneHundredThirtyNineEG_164335096890292317424079262487, phi_oneHundredThirtyNineEG_164335096890292317424079262488, phi_oneHundredThirtyNineEG_164335096890292317424079262489,
    phi_oneHundredThirtyNineEG_164335096890292317424079262490, phi_oneHundredThirtyNineEG_164335096890292317424079262491, phi_oneHundredThirtyNineEG_164335096890292317424079262492,
    phi_oneHundredThirtyNineEG_164335096890292317424079262493, phi_oneHundredThirtyNineEG_164335096890292317424079262494, phi_oneHundredThirtyNineEG_164335096890292317424079262495,
    phi_oneHundredThirtyNineEG_164335096890292317424079262496, phi_oneHundredThirtyNineEG_164335096890292317424079262497, phi_oneHundredThirtyNineEG_164335096890292317424079262498,
    phi_oneHundredThirtyNineEG_164335096890292317424079262499, phi_oneHundredThirtyNineEG_164335096890292317424079262500, phi_oneHundredThirtyNineEG_164335096890292317424079262501
    ]

end TotientTailPeriodKiller
end Erdos249257
