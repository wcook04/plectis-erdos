import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredElevenDEFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredElevenDEFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredElevenDEFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredElevenDEFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredElevenDEFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredElevenDEFastPow a n * oneHundredElevenDEFastPow a n * a else oneHundredElevenDEFastPow a n * oneHundredElevenDEFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredElevenDE_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredElevenDE_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredElevenDE_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredElevenDE_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredElevenDE_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredElevenDE_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredElevenDE_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredElevenDE_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredElevenDE_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredElevenDE_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredElevenDE_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredElevenDE_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredElevenDE_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredElevenDE_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredElevenDE_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredElevenDE_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredElevenDE_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredElevenDE_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredElevenDE_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredElevenDE_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredElevenDE_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredElevenDE_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredElevenDE_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredElevenDE_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredElevenDE_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredElevenDE_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredElevenDE_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredElevenDE_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredElevenDE_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredElevenDE_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredElevenDE_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredElevenDE_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredElevenDE_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredElevenDE_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredElevenDE_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredElevenDE_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredElevenDE_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredElevenDE_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredElevenDE_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredElevenDE_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredElevenDE_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredElevenDE_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredElevenDE_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredElevenDE_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredElevenDE_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredElevenDE_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredElevenDE_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredElevenDE_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredElevenDE_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredElevenDE_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredElevenDE_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredElevenDE_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredElevenDE_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredElevenDE_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredElevenDE_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredElevenDE_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredElevenDE_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredElevenDE_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredElevenDE_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredElevenDE_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredElevenDE_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredElevenDE_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredElevenDE_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredElevenDE_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredElevenDE_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredElevenDE_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredElevenDE_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredElevenDE_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredElevenDE_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredElevenDE_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredElevenDE_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredElevenDE_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredElevenDE_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredElevenDE_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredElevenDE_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredElevenDE_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredElevenDE_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredElevenDE_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredElevenDE_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredElevenDE_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredElevenDE_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredElevenDE_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredElevenDE_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredElevenDE_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredElevenDE_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredElevenDE_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredElevenDE_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredElevenDE_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredElevenDE_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredElevenDE_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredElevenDE_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredElevenDE_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredElevenDE_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredElevenDE_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredElevenDE_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredElevenDE_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredElevenDE_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredElevenDE_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredElevenDE_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredElevenDE_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredElevenDE_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredElevenDE_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredElevenDE_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredElevenDE_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredElevenDE_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredElevenDE_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredElevenDE_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredElevenDE_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredElevenDE_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredElevenDE_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredElevenDE_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredElevenDE_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredElevenDE_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredElevenDE_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredElevenDE_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredElevenDE_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredElevenDE_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredElevenDE_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredElevenDE_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredElevenDE_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredElevenDE_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredElevenDE_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredElevenDE_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredElevenDE_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredElevenDE_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredElevenDE_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredElevenDE_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredElevenDE_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredElevenDE_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredElevenDE_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredElevenDE_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredElevenDE_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredElevenDE_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_oneHundredElevenDE_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredElevenDE_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_oneHundredElevenDE_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredElevenDE_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredElevenDE_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_oneHundredElevenDE_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredElevenDE_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_oneHundredElevenDE_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredElevenDE_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_oneHundredElevenDE_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_oneHundredElevenDE_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredElevenDE_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_oneHundredElevenDE_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredElevenDE_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredElevenDE_2539 : Nat.Prime 2539 := by norm_num

private theorem prime_oneHundredElevenDE_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredElevenDE_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_oneHundredElevenDE_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_oneHundredElevenDE_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_oneHundredElevenDE_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_oneHundredElevenDE_3079 : Nat.Prime 3079 := by norm_num

private theorem prime_oneHundredElevenDE_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_oneHundredElevenDE_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_oneHundredElevenDE_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredElevenDE_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredElevenDE_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredElevenDE_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_oneHundredElevenDE_3343 : Nat.Prime 3343 := by norm_num

private theorem prime_oneHundredElevenDE_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_oneHundredElevenDE_3571 : Nat.Prime 3571 := by norm_num

private theorem prime_oneHundredElevenDE_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_oneHundredElevenDE_3617 : Nat.Prime 3617 := by norm_num

private theorem prime_oneHundredElevenDE_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_oneHundredElevenDE_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_oneHundredElevenDE_3911 : Nat.Prime 3911 := by norm_num

private theorem prime_oneHundredElevenDE_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_oneHundredElevenDE_4271 : Nat.Prime 4271 := by norm_num

private theorem prime_oneHundredElevenDE_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_oneHundredElevenDE_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_oneHundredElevenDE_4373 : Nat.Prime 4373 := by norm_num

private theorem prime_oneHundredElevenDE_4567 : Nat.Prime 4567 := by norm_num

private theorem prime_oneHundredElevenDE_4919 : Nat.Prime 4919 := by norm_num

private theorem prime_oneHundredElevenDE_4943 : Nat.Prime 4943 := by norm_num

private theorem prime_oneHundredElevenDE_4967 : Nat.Prime 4967 := by norm_num

private theorem prime_oneHundredElevenDE_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_oneHundredElevenDE_5273 : Nat.Prime 5273 := by norm_num

private theorem prime_oneHundredElevenDE_5303 : Nat.Prime 5303 := by norm_num

private theorem prime_oneHundredElevenDE_5381 : Nat.Prime 5381 := by norm_num

private theorem prime_oneHundredElevenDE_5503 : Nat.Prime 5503 := by norm_num

private theorem prime_oneHundredElevenDE_5521 : Nat.Prime 5521 := by norm_num

private theorem prime_oneHundredElevenDE_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredElevenDE_5717 : Nat.Prime 5717 := by norm_num

private theorem prime_oneHundredElevenDE_6197 : Nat.Prime 6197 := by norm_num

private theorem prime_oneHundredElevenDE_6257 : Nat.Prime 6257 := by norm_num

private theorem prime_oneHundredElevenDE_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_oneHundredElevenDE_6329 : Nat.Prime 6329 := by norm_num

private theorem prime_oneHundredElevenDE_6379 : Nat.Prime 6379 := by norm_num

private theorem prime_oneHundredElevenDE_6473 : Nat.Prime 6473 := by norm_num

private theorem prime_oneHundredElevenDE_6841 : Nat.Prime 6841 := by norm_num

private theorem prime_oneHundredElevenDE_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredElevenDE_6871 : Nat.Prime 6871 := by norm_num

private theorem prime_oneHundredElevenDE_6907 : Nat.Prime 6907 := by norm_num

private theorem prime_oneHundredElevenDE_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_oneHundredElevenDE_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_oneHundredElevenDE_7121 : Nat.Prime 7121 := by norm_num

private theorem prime_oneHundredElevenDE_7417 : Nat.Prime 7417 := by norm_num

private theorem prime_oneHundredElevenDE_7537 : Nat.Prime 7537 := by norm_num

private theorem prime_oneHundredElevenDE_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_oneHundredElevenDE_7741 : Nat.Prime 7741 := by norm_num

private theorem prime_oneHundredElevenDE_7927 : Nat.Prime 7927 := by norm_num

private theorem prime_oneHundredElevenDE_8053 : Nat.Prime 8053 := by norm_num

private theorem prime_oneHundredElevenDE_8059 : Nat.Prime 8059 := by norm_num

private theorem prime_oneHundredElevenDE_8291 : Nat.Prime 8291 := by norm_num

private theorem prime_oneHundredElevenDE_8963 : Nat.Prime 8963 := by norm_num

private theorem prime_oneHundredElevenDE_9001 : Nat.Prime 9001 := by norm_num

private theorem prime_oneHundredElevenDE_9041 : Nat.Prime 9041 := by norm_num

private theorem prime_oneHundredElevenDE_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_oneHundredElevenDE_9403 : Nat.Prime 9403 := by norm_num

private theorem prime_oneHundredElevenDE_9461 : Nat.Prime 9461 := by norm_num

private theorem prime_oneHundredElevenDE_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredElevenDE_9901 : Nat.Prime 9901 := by norm_num

private theorem prime_oneHundredElevenDE_9923 : Nat.Prime 9923 := by norm_num

private theorem prime_oneHundredElevenDE_10169 : Nat.Prime 10169 := by norm_num

private theorem prime_oneHundredElevenDE_11273 : Nat.Prime 11273 := by norm_num

private theorem prime_oneHundredElevenDE_11299 : Nat.Prime 11299 := by norm_num

private theorem prime_oneHundredElevenDE_11353 : Nat.Prime 11353 := by norm_num

private theorem prime_oneHundredElevenDE_11399 : Nat.Prime 11399 := by norm_num

private theorem prime_oneHundredElevenDE_11909 : Nat.Prime 11909 := by norm_num

private theorem prime_oneHundredElevenDE_11987 : Nat.Prime 11987 := by norm_num

private theorem prime_oneHundredElevenDE_12263 : Nat.Prime 12263 := by norm_num

private theorem prime_oneHundredElevenDE_12277 : Nat.Prime 12277 := by norm_num

private theorem prime_oneHundredElevenDE_12703 : Nat.Prime 12703 := by norm_num

private theorem prime_oneHundredElevenDE_13291 : Nat.Prime 13291 := by norm_num

private theorem prime_oneHundredElevenDE_13417 : Nat.Prime 13417 := by norm_num

private theorem prime_oneHundredElevenDE_14153 : Nat.Prime 14153 := by norm_num

private theorem prime_oneHundredElevenDE_14401 : Nat.Prime 14401 := by norm_num

private theorem prime_oneHundredElevenDE_14867 : Nat.Prime 14867 := by norm_num

private theorem prime_oneHundredElevenDE_15427 : Nat.Prime 15427 := by norm_num

private theorem prime_oneHundredElevenDE_15511 : Nat.Prime 15511 := by norm_num

private theorem prime_oneHundredElevenDE_16187 : Nat.Prime 16187 := by norm_num

private theorem prime_oneHundredElevenDE_16193 : Nat.Prime 16193 := by norm_num

private theorem prime_oneHundredElevenDE_16267 : Nat.Prime 16267 := by norm_num

private theorem prime_oneHundredElevenDE_16273 : Nat.Prime 16273 := by norm_num

private theorem prime_oneHundredElevenDE_16381 : Nat.Prime 16381 := by norm_num

private theorem prime_oneHundredElevenDE_16787 : Nat.Prime 16787 := by norm_num

private theorem prime_oneHundredElevenDE_17093 : Nat.Prime 17093 := by norm_num

private theorem prime_oneHundredElevenDE_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredElevenDE_17291 : Nat.Prime 17291 := by norm_num

private theorem prime_oneHundredElevenDE_17333 : Nat.Prime 17333 := by norm_num

private theorem prime_oneHundredElevenDE_17483 : Nat.Prime 17483 := by norm_num

private theorem prime_oneHundredElevenDE_18521 : Nat.Prime 18521 := by norm_num

private theorem prime_oneHundredElevenDE_18749 : Nat.Prime 18749 := by norm_num

private theorem prime_oneHundredElevenDE_18757 : Nat.Prime 18757 := by norm_num

private theorem prime_oneHundredElevenDE_20533 : Nat.Prime 20533 := by norm_num

private theorem prime_oneHundredElevenDE_20593 : Nat.Prime 20593 := by norm_num

private theorem prime_oneHundredElevenDE_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredElevenDE_21773 : Nat.Prime 21773 := by norm_num

private theorem prime_oneHundredElevenDE_22277 : Nat.Prime 22277 := by norm_num

private theorem prime_oneHundredElevenDE_22391 : Nat.Prime 22391 := by norm_num

private theorem prime_oneHundredElevenDE_22741 : Nat.Prime 22741 := by norm_num

private theorem prime_oneHundredElevenDE_23879 : Nat.Prime 23879 := by norm_num

private theorem prime_oneHundredElevenDE_24841 : Nat.Prime 24841 := by norm_num

private theorem prime_oneHundredElevenDE_24917 : Nat.Prime 24917 := by norm_num

private theorem prime_oneHundredElevenDE_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredElevenDE_25639 : Nat.Prime 25639 := by norm_num

private theorem prime_oneHundredElevenDE_26293 : Nat.Prime 26293 := by norm_num

private theorem prime_oneHundredElevenDE_26641 : Nat.Prime 26641 := by norm_num

private theorem prime_oneHundredElevenDE_26717 : Nat.Prime 26717 := by norm_num

private theorem prime_oneHundredElevenDE_26893 : Nat.Prime 26893 := by norm_num

private theorem prime_oneHundredElevenDE_29483 : Nat.Prime 29483 := by norm_num

private theorem prime_oneHundredElevenDE_30269 : Nat.Prime 30269 := by norm_num

private theorem prime_oneHundredElevenDE_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredElevenDE_31277 : Nat.Prime 31277 := by norm_num

private theorem prime_oneHundredElevenDE_33569 : Nat.Prime 33569 := by norm_num

private theorem prime_oneHundredElevenDE_33757 : Nat.Prime 33757 := by norm_num

private theorem prime_oneHundredElevenDE_36017 : Nat.Prime 36017 := by norm_num

private theorem prime_oneHundredElevenDE_37049 : Nat.Prime 37049 := by norm_num

private theorem prime_oneHundredElevenDE_39163 : Nat.Prime 39163 := by norm_num

private theorem prime_oneHundredElevenDE_41617 : Nat.Prime 41617 := by norm_num

private theorem prime_oneHundredElevenDE_42307 : Nat.Prime 42307 := by norm_num

private theorem prime_oneHundredElevenDE_43271 : Nat.Prime 43271 := by norm_num

private theorem prime_oneHundredElevenDE_45317 : Nat.Prime 45317 := by norm_num

private theorem prime_oneHundredElevenDE_45557 : Nat.Prime 45557 := by norm_num

private theorem prime_oneHundredElevenDE_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredElevenDE_51929 : Nat.Prime 51929 := by norm_num

private theorem prime_oneHundredElevenDE_53281 : Nat.Prime 53281 := by norm_num

private theorem prime_oneHundredElevenDE_54011 : Nat.Prime 54011 := by norm_num

private theorem prime_oneHundredElevenDE_54941 : Nat.Prime 54941 := by norm_num

private theorem prime_oneHundredElevenDE_55871 : Nat.Prime 55871 := by norm_num

private theorem prime_oneHundredElevenDE_57107 : Nat.Prime 57107 := by norm_num

private theorem prime_oneHundredElevenDE_59999 : Nat.Prime 59999 := by norm_num

private theorem prime_oneHundredElevenDE_62581 : Nat.Prime 62581 := by norm_num

private theorem prime_oneHundredElevenDE_63409 : Nat.Prime 63409 := by norm_num

private theorem prime_oneHundredElevenDE_65551 : Nat.Prime 65551 := by norm_num

private theorem prime_oneHundredElevenDE_67339 : Nat.Prime 67339 := by norm_num

private theorem prime_oneHundredElevenDE_75937 : Nat.Prime 75937 := by norm_num

private theorem prime_oneHundredElevenDE_79333 : Nat.Prime 79333 := by norm_num

private theorem prime_oneHundredElevenDE_82223 : Nat.Prime 82223 := by norm_num

private theorem prime_oneHundredElevenDE_83537 : Nat.Prime 83537 := by norm_num

private theorem prime_oneHundredElevenDE_84913 : Nat.Prime 84913 := by norm_num

private theorem prime_oneHundredElevenDE_87473 : Nat.Prime 87473 := by norm_num

private theorem prime_oneHundredElevenDE_92593 : Nat.Prime 92593 := by norm_num

private theorem prime_oneHundredElevenDE_101839 : Nat.Prime 101839 := by norm_num

private theorem prime_oneHundredElevenDE_103237 : Nat.Prime 103237 := by norm_num

private theorem prime_oneHundredElevenDE_105529 : Nat.Prime 105529 := by norm_num

private theorem prime_oneHundredElevenDE_106181 : Nat.Prime 106181 := by norm_num

private theorem prime_oneHundredElevenDE_108287 : Nat.Prime 108287 := by norm_num

private theorem prime_oneHundredElevenDE_109253 : Nat.Prime 109253 := by norm_num

private theorem prime_oneHundredElevenDE_110479 : Nat.Prime 110479 := by norm_num

private theorem prime_oneHundredElevenDE_119033 : Nat.Prime 119033 := by norm_num

private theorem prime_oneHundredElevenDE_131519 : Nat.Prime 131519 := by norm_num

private theorem prime_oneHundredElevenDE_135581 : Nat.Prime 135581 := by norm_num

private theorem prime_oneHundredElevenDE_135929 : Nat.Prime 135929 := by norm_num

private theorem prime_oneHundredElevenDE_139333 : Nat.Prime 139333 := by norm_num

private theorem prime_oneHundredElevenDE_141233 : Nat.Prime 141233 := by norm_num

private theorem prime_oneHundredElevenDE_146921 : Nat.Prime 146921 := by norm_num

private theorem prime_oneHundredElevenDE_152563 : Nat.Prime 152563 := by norm_num

private theorem prime_oneHundredElevenDE_154667 : Nat.Prime 154667 := by norm_num

private theorem prime_oneHundredElevenDE_160579 : Nat.Prime 160579 := by norm_num

private theorem prime_oneHundredElevenDE_163909 : Nat.Prime 163909 := by norm_num

private theorem prime_oneHundredElevenDE_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredElevenDE_171469 : Nat.Prime 171469 := by norm_num

private theorem prime_oneHundredElevenDE_172663 : Nat.Prime 172663 := by norm_num

private theorem prime_oneHundredElevenDE_176333 : Nat.Prime 176333 := by norm_num

private theorem prime_oneHundredElevenDE_199673 : Nat.Prime 199673 := by norm_num

private theorem prime_oneHundredElevenDE_203429 : Nat.Prime 203429 := by norm_num

private theorem prime_oneHundredElevenDE_208141 : Nat.Prime 208141 := by norm_num

private theorem prime_oneHundredElevenDE_215399 : Nat.Prime 215399 := by norm_num

private theorem prime_oneHundredElevenDE_220889 : Nat.Prime 220889 := by norm_num

private theorem prime_oneHundredElevenDE_223319 : Nat.Prime 223319 := by norm_num

private theorem prime_oneHundredElevenDE_237331 : Nat.Prime 237331 := by norm_num

private theorem prime_oneHundredElevenDE_247997 : Nat.Prime 247997 := by norm_num

private theorem prime_oneHundredElevenDE_251857 : Nat.Prime 251857 := by norm_num

private theorem prime_oneHundredElevenDE_252293 : Nat.Prime 252293 := by norm_num

private theorem prime_oneHundredElevenDE_257657 : Nat.Prime 257657 := by norm_num

private theorem prime_oneHundredElevenDE_265567 : Nat.Prime 265567 := by norm_num

private theorem prime_oneHundredElevenDE_267647 : Nat.Prime 267647 := by norm_num

private theorem prime_oneHundredElevenDE_278219 : Nat.Prime 278219 := by norm_num

private theorem prime_oneHundredElevenDE_282089 : Nat.Prime 282089 := by norm_num

private theorem prime_oneHundredElevenDE_285101 : Nat.Prime 285101 := by norm_num

private theorem prime_oneHundredElevenDE_287579 : Nat.Prime 287579 := by norm_num

private theorem prime_oneHundredElevenDE_309437 : Nat.Prime 309437 := by norm_num

private theorem prime_oneHundredElevenDE_336491 : Nat.Prime 336491 := by norm_num

private theorem prime_oneHundredElevenDE_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredElevenDE_347747 : Nat.Prime 347747 := by norm_num

private theorem prime_oneHundredElevenDE_364979 : Nat.Prime 364979 := by norm_num

private theorem prime_oneHundredElevenDE_368647 : Nat.Prime 368647 := by norm_num

private theorem prime_oneHundredElevenDE_392099 : Nat.Prime 392099 := by norm_num

private theorem prime_oneHundredElevenDE_428401 : Nat.Prime 428401 := by norm_num

private theorem prime_oneHundredElevenDE_456119 : Nat.Prime 456119 := by norm_num

private theorem prime_oneHundredElevenDE_462013 : Nat.Prime 462013 := by norm_num

private theorem prime_oneHundredElevenDE_500693 : Nat.Prime 500693 := by norm_num

private theorem prime_oneHundredElevenDE_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredElevenDE_571369 : Nat.Prime 571369 := by norm_num

private theorem prime_oneHundredElevenDE_652507 : Nat.Prime 652507 := by norm_num

private theorem prime_oneHundredElevenDE_667519 : Nat.Prime 667519 := by norm_num

private theorem prime_oneHundredElevenDE_691267 : Nat.Prime 691267 := by norm_num

private theorem prime_oneHundredElevenDE_695207 : Nat.Prime 695207 := by norm_num

private theorem prime_oneHundredElevenDE_695749 : Nat.Prime 695749 := by norm_num

private theorem prime_oneHundredElevenDE_698077 : Nat.Prime 698077 := by norm_num

private theorem prime_oneHundredElevenDE_724847 : Nat.Prime 724847 := by norm_num

private theorem prime_oneHundredElevenDE_749803 : Nat.Prime 749803 := by norm_num

private theorem prime_oneHundredElevenDE_775807 : Nat.Prime 775807 := by norm_num

private theorem prime_oneHundredElevenDE_831529 : Nat.Prime 831529 := by norm_num

private theorem prime_oneHundredElevenDE_903607 : Nat.Prime 903607 := by norm_num

private theorem prime_oneHundredElevenDE_952009 : Nat.Prime 952009 := by norm_num

private theorem prime_oneHundredElevenDE_1016581 : Nat.Prime 1016581 := by norm_num

private theorem prime_oneHundredElevenDE_1027853 : Nat.Prime 1027853 := by norm_num

private theorem prime_oneHundredElevenDE_1080973 : Nat.Prime 1080973 := by norm_num

private theorem prime_oneHundredElevenDE_1133537 : Nat.Prime 1133537 := by norm_num

private theorem prime_oneHundredElevenDE_1160983 : Nat.Prime 1160983 := by norm_num

private theorem prime_oneHundredElevenDE_1199663 : Nat.Prime 1199663 := by norm_num

private theorem prime_oneHundredElevenDE_1220507 : Nat.Prime 1220507 := by norm_num

private theorem prime_oneHundredElevenDE_1252429 : Nat.Prime 1252429 := by norm_num

private theorem prime_oneHundredElevenDE_1277803 : Nat.Prime 1277803 := by norm_num

private theorem prime_oneHundredElevenDE_1389673 : Nat.Prime 1389673 := by norm_num

private theorem prime_oneHundredElevenDE_1437251 : Nat.Prime 1437251 := by norm_num

private theorem prime_oneHundredElevenDE_1769947 : Nat.Prime 1769947 := by norm_num

private theorem prime_oneHundredElevenDE_1901191 : Nat.Prime 1901191 := by norm_num

private theorem prime_oneHundredElevenDE_1902643 : Nat.Prime 1902643 := by norm_num

private theorem prime_oneHundredElevenDE_1993357 : Nat.Prime 1993357 := by norm_num

private theorem prime_oneHundredElevenDE_2125933 : Nat.Prime 2125933 := by norm_num

private theorem prime_oneHundredElevenDE_2291717 : Nat.Prime 2291717 := by norm_num

private theorem prime_oneHundredElevenDE_2433853 : Nat.Prime 2433853 := by norm_num

private theorem prime_oneHundredElevenDE_2440447 : Nat.Prime 2440447 := by norm_num

private theorem prime_oneHundredElevenDE_2494469 : Nat.Prime 2494469 := by norm_num

private theorem prime_oneHundredElevenDE_2613833 : Nat.Prime 2613833 := by norm_num

private theorem prime_oneHundredElevenDE_2698691 : Nat.Prime 2698691 := by norm_num

private theorem prime_oneHundredElevenDE_2712713 : Nat.Prime 2712713 := by norm_num

private theorem prime_oneHundredElevenDE_2824631 : Nat.Prime 2824631 := by norm_num

private theorem prime_oneHundredElevenDE_3073757 : Nat.Prime 3073757 := by norm_num

private theorem prime_oneHundredElevenDE_3165289 : Nat.Prime 3165289 := by norm_num

private theorem prime_oneHundredElevenDE_3172423 : Nat.Prime 3172423 := by norm_num

private theorem prime_oneHundredElevenDE_3323561 : Nat.Prime 3323561 := by norm_num

private theorem prime_oneHundredElevenDE_3360299 : Nat.Prime 3360299 := by norm_num

private theorem prime_oneHundredElevenDE_3664447 : Nat.Prime 3664447 := by norm_num

private theorem prime_oneHundredElevenDE_4162421 : Nat.Prime 4162421 := by norm_num

private theorem prime_oneHundredElevenDE_4614341 : Nat.Prime 4614341 := by norm_num

private theorem prime_oneHundredElevenDE_4618993 : Nat.Prime 4618993 := by norm_num

private theorem prime_oneHundredElevenDE_4854599 : Nat.Prime 4854599 := by norm_num

private theorem prime_oneHundredElevenDE_4956509 : Nat.Prime 4956509 := by norm_num

private theorem prime_oneHundredElevenDE_5273381 : Nat.Prime 5273381 := by norm_num

private theorem prime_oneHundredElevenDE_5688317 : Nat.Prime 5688317 := by norm_num

private theorem prime_oneHundredElevenDE_5691509 : Nat.Prime 5691509 := by norm_num

private theorem prime_oneHundredElevenDE_5924987 : Nat.Prime 5924987 := by norm_num

private theorem prime_oneHundredElevenDE_6203251 : Nat.Prime 6203251 := by norm_num

private theorem prime_oneHundredElevenDE_6245311 : Nat.Prime 6245311 := by norm_num

private theorem prime_oneHundredElevenDE_6307841 : Nat.Prime 6307841 := by norm_num

private theorem prime_oneHundredElevenDE_6894161 : Nat.Prime 6894161 := by norm_num

private theorem prime_oneHundredElevenDE_8570411 : Nat.Prime 8570411 := by norm_num

private theorem prime_oneHundredElevenDE_9434767 : Nat.Prime 9434767 := by norm_num

private theorem prime_oneHundredElevenDE_9886937 : Nat.Prime 9886937 := by norm_num

private theorem prime_oneHundredElevenDE_9932009 : Nat.Prime 9932009 := by norm_num

private theorem prime_oneHundredElevenDE_10432259 : Nat.Prime 10432259 := by norm_num

private theorem prime_oneHundredElevenDE_10728017 : Nat.Prime 10728017 := by norm_num

private theorem prime_oneHundredElevenDE_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredElevenDE_10978921 : Nat.Prime 10978921 := by norm_num

private theorem prime_oneHundredElevenDE_11234243 : Nat.Prime 11234243 := by norm_num

private theorem prime_oneHundredElevenDE_12263353 : Nat.Prime 12263353 := by norm_num

private theorem prime_oneHundredElevenDE_12823777 : Nat.Prime 12823777 := by norm_num

private theorem prime_oneHundredElevenDE_13255499 : Nat.Prime 13255499 := by norm_num

private theorem prime_oneHundredElevenDE_14050649 : Nat.Prime 14050649 := by norm_num

private theorem prime_oneHundredElevenDE_14097409 : Nat.Prime 14097409 := by norm_num

private theorem prime_oneHundredElevenDE_14556011 : Nat.Prime 14556011 := by norm_num

private theorem prime_oneHundredElevenDE_15974227 : Nat.Prime 15974227 := by norm_num

private theorem prime_oneHundredElevenDE_16462021 : Nat.Prime 16462021 := by norm_num

private theorem prime_oneHundredElevenDE_16593677 : Nat.Prime 16593677 := by norm_num

private theorem prime_oneHundredElevenDE_16965149 : Nat.Prime 16965149 := by norm_num

private theorem prime_oneHundredElevenDE_17135687 : Nat.Prime 17135687 := by norm_num

private theorem prime_oneHundredElevenDE_19274603 : Nat.Prime 19274603 := by norm_num

private theorem prime_oneHundredElevenDE_20831827 : Nat.Prime 20831827 := by norm_num

private theorem prime_oneHundredElevenDE_21563639 : Nat.Prime 21563639 := by norm_num

private theorem prime_oneHundredElevenDE_21963433 : Nat.Prime 21963433 := by norm_num

private theorem prime_oneHundredElevenDE_22191469 : Nat.Prime 22191469 := by norm_num

private theorem prime_oneHundredElevenDE_22428871 : Nat.Prime 22428871 := by norm_num

private theorem prime_oneHundredElevenDE_24377317 : Nat.Prime 24377317 := by norm_num

private theorem prime_oneHundredElevenDE_24494243 : Nat.Prime 24494243 := by norm_num

private theorem prime_oneHundredElevenDE_25657019 : Nat.Prime 25657019 := by norm_num

private theorem prime_oneHundredElevenDE_28162991 : Nat.Prime 28162991 := by norm_num

private theorem prime_oneHundredElevenDE_29674847 : Nat.Prime 29674847 := by norm_num

private theorem prime_oneHundredElevenDE_29721271 : Nat.Prime 29721271 := by norm_num

private theorem prime_oneHundredElevenDE_33637193 : Nat.Prime 33637193 := by
  apply lucas_primality 33637193 (3 : ZMod 33637193)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (79333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (79333, 1)] : List FactorBlock).map factorBlockValue).prod) = 33637193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_53
      · exact prime_oneHundredElevenDE_79333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33637193) ^ 16818596 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 33637193) ^ 634664 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 33637193) ^ 424 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_35991283 : Nat.Prime 35991283 := by
  apply lucas_primality 35991283 (2 : ZMod 35991283)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (491, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (491, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 35991283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_491
      · exact prime_oneHundredElevenDE_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35991283) ^ 17995641 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 35991283) ^ 11997094 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 35991283) ^ 1894278 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 35991283) ^ 73302 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 35991283) ^ 55974 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_41111293 : Nat.Prime 41111293 := by
  apply lucas_primality 41111293 (2 : ZMod 41111293)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (92593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (92593, 1)] : List FactorBlock).map factorBlockValue).prod) = 41111293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_37
      · exact prime_oneHundredElevenDE_92593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41111293) ^ 20555646 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41111293) ^ 13703764 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41111293) ^ 1111116 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41111293) ^ 444 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_44217163 : Nat.Prime 44217163 := by
  apply lucas_primality 44217163 (5 : ZMod 44217163)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (223319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (223319, 1)] : List FactorBlock).map factorBlockValue).prod) = 44217163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_223319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44217163) ^ 22108581 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 44217163) ^ 14739054 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 44217163) ^ 4019742 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 44217163) ^ 198 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_46163069 : Nat.Prime 46163069 := by
  apply lucas_primality 46163069 (2 : ZMod 46163069)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (241, 1), (6841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (241, 1), (6841, 1)] : List FactorBlock).map factorBlockValue).prod) = 46163069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_241
      · exact prime_oneHundredElevenDE_6841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46163069) ^ 23081534 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46163069) ^ 6594724 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46163069) ^ 191548 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46163069) ^ 6748 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_50411887 : Nat.Prime 50411887 := by
  apply lucas_primality 50411887 (3 : ZMod 50411887)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (171469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (171469, 1)] : List FactorBlock).map factorBlockValue).prod) = 50411887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_171469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50411887) ^ 25205943 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 50411887) ^ 16803962 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 50411887) ^ 7201698 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 50411887) ^ 294 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_51139609 : Nat.Prime 51139609 := by
  apply lucas_primality 51139609 (7 : ZMod 51139609)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (163909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (163909, 1)] : List FactorBlock).map factorBlockValue).prod) = 51139609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_163909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 51139609) ^ 25569804 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51139609) ^ 17046536 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51139609) ^ 3933816 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51139609) ^ 312 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_56063317 : Nat.Prime 56063317 := by
  apply lucas_primality 56063317 (6 : ZMod 56063317)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (881, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (881, 1), (5303, 1)] : List FactorBlock).map factorBlockValue).prod) = 56063317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_881
      · exact prime_oneHundredElevenDE_5303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 56063317) ^ 28031658 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 56063317) ^ 18687772 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 56063317) ^ 63636 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 56063317) ^ 10572 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_66529873 : Nat.Prime 66529873 := by
  apply lucas_primality 66529873 (10 : ZMod 66529873)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (462013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (462013, 1)] : List FactorBlock).map factorBlockValue).prod) = 66529873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_462013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 66529873) ^ 33264936 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 66529873) ^ 22176624 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 66529873) ^ 144 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_68887661 : Nat.Prime 68887661 := by
  apply lucas_primality 68887661 (2 : ZMod 68887661)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (131, 1), (26293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (131, 1), (26293, 1)] : List FactorBlock).map factorBlockValue).prod) = 68887661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_131
      · exact prime_oneHundredElevenDE_26293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68887661) ^ 34443830 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 68887661) ^ 13777532 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 68887661) ^ 525860 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 68887661) ^ 2620 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_68889851 : Nat.Prime 68889851 := by
  apply lucas_primality 68889851 (2 : ZMod 68889851)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (241, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (241, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod) = 68889851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_241
      · exact prime_oneHundredElevenDE_5717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68889851) ^ 34444925 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 68889851) ^ 13777970 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 68889851) ^ 285850 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 68889851) ^ 12050 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_69159911 : Nat.Prime 69159911 := by
  apply lucas_primality 69159911 (7 : ZMod 69159911)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (43, 1), (9461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (43, 1), (9461, 1)] : List FactorBlock).map factorBlockValue).prod) = 69159911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_43
      · exact prime_oneHundredElevenDE_9461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 69159911) ^ 34579955 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 69159911) ^ 13831982 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 69159911) ^ 4068230 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 69159911) ^ 1608370 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 69159911) ^ 7310 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_73145341 : Nat.Prime 73145341 := by
  apply lucas_primality 73145341 (10 : ZMod 73145341)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (383, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (383, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) = 73145341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_383
      · exact prime_oneHundredElevenDE_1061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 73145341) ^ 36572670 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 73145341) ^ 24381780 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 73145341) ^ 14629068 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 73145341) ^ 190980 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 73145341) ^ 68940 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_74045339 : Nat.Prime 74045339 := by
  apply lucas_primality 74045339 (2 : ZMod 74045339)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (97, 1), (6257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (97, 1), (6257, 1)] : List FactorBlock).map factorBlockValue).prod) = 74045339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_97
      · exact prime_oneHundredElevenDE_6257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74045339) ^ 37022669 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 74045339) ^ 1213858 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 74045339) ^ 763354 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 74045339) ^ 11834 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_79636439 : Nat.Prime 79636439 := by
  apply lucas_primality 79636439 (7 : ZMod 79636439)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5688317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5688317, 1)] : List FactorBlock).map factorBlockValue).prod) = 79636439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_5688317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 79636439) ^ 39818219 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 79636439) ^ 11376634 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 79636439) ^ 14 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_85571449 : Nat.Prime 85571449 := by
  apply lucas_primality 85571449 (7 : ZMod 85571449)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1789, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1789, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) = 85571449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_1789
      · exact prime_oneHundredElevenDE_1993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 85571449) ^ 42785724 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 85571449) ^ 28523816 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 85571449) ^ 47832 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 85571449) ^ 42936 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_88765877 : Nat.Prime 88765877 := by
  apply lucas_primality 88765877 (2 : ZMod 88765877)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (22191469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (22191469, 1)] : List FactorBlock).map factorBlockValue).prod) = 88765877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_22191469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 88765877) ^ 44382938 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 88765877) ^ 4 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_95453857 : Nat.Prime 95453857 := by
  apply lucas_primality 95453857 (5 : ZMod 95453857)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (110479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (110479, 1)] : List FactorBlock).map factorBlockValue).prod) = 95453857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_110479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 95453857) ^ 47726928 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 95453857) ^ 31817952 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 95453857) ^ 864 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_96673667 : Nat.Prime 96673667 := by
  apply lucas_primality 96673667 (2 : ZMod 96673667)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (347747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (347747, 1)] : List FactorBlock).map factorBlockValue).prod) = 96673667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_139
      · exact prime_oneHundredElevenDE_347747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96673667) ^ 48336833 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 96673667) ^ 695494 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 96673667) ^ 278 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_98937437 : Nat.Prime 98937437 := by
  apply lucas_primality 98937437 (2 : ZMod 98937437)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1902643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1902643, 1)] : List FactorBlock).map factorBlockValue).prod) = 98937437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_1902643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 98937437) ^ 49468718 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 98937437) ^ 7610572 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 98937437) ^ 52 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_110407393 : Nat.Prime 110407393 := by
  apply lucas_primality 110407393 (5 : ZMod 110407393)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (523, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (523, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 110407393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_523
      · exact prime_oneHundredElevenDE_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 110407393) ^ 55203696 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 110407393) ^ 36802464 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 110407393) ^ 211104 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 110407393) ^ 150624 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_126445663 : Nat.Prime 126445663 := by
  apply lucas_primality 126445663 (3 : ZMod 126445663)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (79, 1), (12703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (79, 1), (12703, 1)] : List FactorBlock).map factorBlockValue).prod) = 126445663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_79
      · exact prime_oneHundredElevenDE_12703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 126445663) ^ 63222831 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 126445663) ^ 42148554 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 126445663) ^ 18063666 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 126445663) ^ 1600578 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 126445663) ^ 9954 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_138417119 : Nat.Prime 138417119 := by
  apply lucas_primality 138417119 (7 : ZMod 138417119)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (9886937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (9886937, 1)] : List FactorBlock).map factorBlockValue).prod) = 138417119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_9886937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 138417119) ^ 69208559 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 138417119) ^ 19773874 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 138417119) ^ 14 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_148139759 : Nat.Prime 148139759 := by
  apply lucas_primality 148139759 (11 : ZMod 148139759)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (97, 1), (151, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (97, 1), (151, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 148139759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_97
      · exact prime_oneHundredElevenDE_151
      · exact prime_oneHundredElevenDE_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 148139759) ^ 74069879 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 148139759) ^ 11395366 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 148139759) ^ 1527214 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 148139759) ^ 981058 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 148139759) ^ 380822 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_162430501 : Nat.Prime 162430501 := by
  apply lucas_primality 162430501 (10 : ZMod 162430501)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (108287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (108287, 1)] : List FactorBlock).map factorBlockValue).prod) = 162430501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_108287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 162430501) ^ 81215250 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 162430501) ^ 54143500 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 162430501) ^ 32486100 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 162430501) ^ 1500 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_163942871 : Nat.Prime 163942871 := by
  apply lucas_primality 163942871 (7 : ZMod 163942871)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (257, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (257, 1), (701, 1)] : List FactorBlock).map factorBlockValue).prod) = 163942871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_257
      · exact prime_oneHundredElevenDE_701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 163942871) ^ 81971435 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 163942871) ^ 32788574 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 163942871) ^ 23420410 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 163942871) ^ 12610990 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 163942871) ^ 637910 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 163942871) ^ 233870 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_184894921 : Nat.Prime 184894921 := by
  apply lucas_primality 184894921 (17 : ZMod 184894921)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (37, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (37, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 184894921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_37
      · exact prime_oneHundredElevenDE_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 184894921) ^ 92447460 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (17 : ZMod 184894921) ^ 61631640 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (17 : ZMod 184894921) ^ 36978984 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (17 : ZMod 184894921) ^ 26413560 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (17 : ZMod 184894921) ^ 4997160 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (17 : ZMod 184894921) ^ 279720 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_199576873 : Nat.Prime 199576873 := by
  apply lucas_primality 199576873 (5 : ZMod 199576873)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 7), (11, 1), (17, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 7), (11, 1), (17, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 199576873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 199576873) ^ 99788436 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 199576873) ^ 66525624 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 199576873) ^ 18143352 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 199576873) ^ 11739816 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 199576873) ^ 3271752 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_213577093 : Nat.Prime 213577093 := by
  apply lucas_primality 213577093 (2 : ZMod 213577093)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (103, 1), (239, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (103, 1), (239, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 213577093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_103
      · exact prime_oneHundredElevenDE_239
      · exact prime_oneHundredElevenDE_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 213577093) ^ 106788546 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 213577093) ^ 71192364 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 213577093) ^ 2073564 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 213577093) ^ 893628 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 213577093) ^ 886212 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_222003791 : Nat.Prime 222003791 := by
  apply lucas_primality 222003791 (7 : ZMod 222003791)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (431, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (431, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) = 222003791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_431
      · exact prime_oneHundredElevenDE_2711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 222003791) ^ 111001895 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 222003791) ^ 44400758 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 222003791) ^ 11684410 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 222003791) ^ 515090 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 222003791) ^ 81890 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_238368217 : Nat.Prime 238368217 := by
  apply lucas_primality 238368217 (7 : ZMod 238368217)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (9932009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (9932009, 1)] : List FactorBlock).map factorBlockValue).prod) = 238368217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_9932009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 238368217) ^ 119184108 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 238368217) ^ 79456072 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 238368217) ^ 24 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_249425623 : Nat.Prime 249425623 := by
  apply lucas_primality 249425623 (3 : ZMod 249425623)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (4618993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (4618993, 1)] : List FactorBlock).map factorBlockValue).prod) = 249425623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_4618993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 249425623) ^ 124712811 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 249425623) ^ 83141874 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 249425623) ^ 54 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_249569597 : Nat.Prime 249569597 := by
  apply lucas_primality 249569597 (2 : ZMod 249569597)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (2712713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (2712713, 1)] : List FactorBlock).map factorBlockValue).prod) = 249569597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_2712713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 249569597) ^ 124784798 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 249569597) ^ 10850852 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 249569597) ^ 92 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_269146453 : Nat.Prime 269146453 := by
  apply lucas_primality 269146453 (2 : ZMod 269146453)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (22428871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (22428871, 1)] : List FactorBlock).map factorBlockValue).prod) = 269146453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_22428871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 269146453) ^ 134573226 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 269146453) ^ 89715484 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 269146453) ^ 12 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_277287511 : Nat.Prime 277287511 := by
  apply lucas_primality 277287511 (6 : ZMod 277287511)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (41, 1), (89, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (41, 1), (89, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 277287511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_89
      · exact prime_oneHundredElevenDE_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 277287511) ^ 138643755 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 92429170 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 55457502 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 16311030 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 6763110 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 3115590 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 1860990 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_312967771 : Nat.Prime 312967771 := by
  apply lucas_primality 312967771 (2 : ZMod 312967771)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (10432259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (10432259, 1)] : List FactorBlock).map factorBlockValue).prod) = 312967771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_10432259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 312967771) ^ 156483885 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 312967771) ^ 104322590 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 312967771) ^ 62593554 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 312967771) ^ 30 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_337215577 : Nat.Prime 337215577 := by
  apply lucas_primality 337215577 (5 : ZMod 337215577)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (14050649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (14050649, 1)] : List FactorBlock).map factorBlockValue).prod) = 337215577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_14050649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 337215577) ^ 168607788 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 337215577) ^ 112405192 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 337215577) ^ 24 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_356019271 : Nat.Prime 356019271 := by
  apply lucas_primality 356019271 (3 : ZMod 356019271)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (698077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (698077, 1)] : List FactorBlock).map factorBlockValue).prod) = 356019271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_698077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 356019271) ^ 178009635 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 356019271) ^ 118673090 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 356019271) ^ 71203854 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 356019271) ^ 20942310 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 356019271) ^ 510 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_393024829 : Nat.Prime 393024829 := by
  apply lucas_primality 393024829 (2 : ZMod 393024829)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (203429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (203429, 1)] : List FactorBlock).map factorBlockValue).prod) = 393024829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_203429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 393024829) ^ 196512414 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 393024829) ^ 131008276 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 393024829) ^ 56146404 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 393024829) ^ 17088036 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 393024829) ^ 1932 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_398273363 : Nat.Prime 398273363 := by
  apply lucas_primality 398273363 (2 : ZMod 398273363)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3319, 1), (59999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3319, 1), (59999, 1)] : List FactorBlock).map factorBlockValue).prod) = 398273363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3319
      · exact prime_oneHundredElevenDE_59999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 398273363) ^ 199136681 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 398273363) ^ 119998 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 398273363) ^ 6638 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_407263963 : Nat.Prime 407263963 := by
  apply lucas_primality 407263963 (12 : ZMod 407263963)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (233, 1), (41617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (233, 1), (41617, 1)] : List FactorBlock).map factorBlockValue).prod) = 407263963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_233
      · exact prime_oneHundredElevenDE_41617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 407263963) ^ 203631981 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (12 : ZMod 407263963) ^ 135754654 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (12 : ZMod 407263963) ^ 58180566 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (12 : ZMod 407263963) ^ 1747914 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (12 : ZMod 407263963) ^ 9786 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_438791707 : Nat.Prime 438791707 := by
  apply lucas_primality 438791707 (3 : ZMod 438791707)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24377317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24377317, 1)] : List FactorBlock).map factorBlockValue).prod) = 438791707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_24377317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 438791707) ^ 219395853 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 438791707) ^ 146263902 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 438791707) ^ 18 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_518727653 : Nat.Prime 518727653 := by
  apply lucas_primality 518727653 (2 : ZMod 518727653)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (2125933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (2125933, 1)] : List FactorBlock).map factorBlockValue).prod) = 518727653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_2125933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 518727653) ^ 259363826 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 518727653) ^ 8503732 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 518727653) ^ 244 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_557767883 : Nat.Prime 557767883 := by
  apply lucas_primality 557767883 (2 : ZMod 557767883)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (5691509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (5691509, 1)] : List FactorBlock).map factorBlockValue).prod) = 557767883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_5691509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 557767883) ^ 278883941 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 557767883) ^ 79681126 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 557767883) ^ 98 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_632350777 : Nat.Prime 632350777 := by
  apply lucas_primality 632350777 (5 : ZMod 632350777)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (43, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (43, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) = 632350777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_43
      · exact prime_oneHundredElevenDE_26641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 632350777) ^ 316175388 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 632350777) ^ 210783592 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 632350777) ^ 27493512 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 632350777) ^ 14705832 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 632350777) ^ 23736 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_649571509 : Nat.Prime 649571509 := by
  apply lucas_primality 649571509 (2 : ZMod 649571509)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (347, 1), (17333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (347, 1), (17333, 1)] : List FactorBlock).map factorBlockValue).prod) = 649571509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_347
      · exact prime_oneHundredElevenDE_17333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 649571509) ^ 324785754 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 649571509) ^ 216523836 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 649571509) ^ 1871964 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 649571509) ^ 37476 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_17203
      · exact prime_oneHundredElevenDE_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_798307493 : Nat.Prime 798307493 := by
  apply lucas_primality 798307493 (2 : ZMod 798307493)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (199576873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (199576873, 1)] : List FactorBlock).map factorBlockValue).prod) = 798307493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_199576873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 798307493) ^ 399153746 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 798307493) ^ 4 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_822306161 : Nat.Prime 822306161 := by
  apply lucas_primality 822306161 (3 : ZMod 822306161)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (761, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (761, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) = 822306161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_761
      · exact prime_oneHundredElevenDE_1039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 822306161) ^ 411153080 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 822306161) ^ 164461232 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 822306161) ^ 63254320 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 822306161) ^ 1080560 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 822306161) ^ 791440 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_893367389 : Nat.Prime 893367389 := by
  apply lucas_primality 893367389 (2 : ZMod 893367389)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 2), (265567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 2), (265567, 1)] : List FactorBlock).map factorBlockValue).prod) = 893367389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_29
      · exact prime_oneHundredElevenDE_265567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 893367389) ^ 446683694 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 893367389) ^ 30805772 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 893367389) ^ 3364 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_908057209 : Nat.Prime 908057209 := by
  apply lucas_primality 908057209 (13 : ZMod 908057209)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (1220507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (1220507, 1)] : List FactorBlock).map factorBlockValue).prod) = 908057209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_1220507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 908057209) ^ 454028604 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 908057209) ^ 302685736 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 908057209) ^ 29292168 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 908057209) ^ 744 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_974583007 : Nat.Prime 974583007 := by
  apply lucas_primality 974583007 (3 : ZMod 974583007)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (162430501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (162430501, 1)] : List FactorBlock).map factorBlockValue).prod) = 974583007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_162430501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 974583007) ^ 487291503 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 974583007) ^ 324861002 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 974583007) ^ 6 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1118543537 : Nat.Prime 1118543537 := by
  apply lucas_primality 1118543537 (3 : ZMod 1118543537)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (821, 1), (7741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (821, 1), (7741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1118543537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_821
      · exact prime_oneHundredElevenDE_7741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1118543537) ^ 559271768 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118543537) ^ 101685776 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118543537) ^ 1362416 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118543537) ^ 144496 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1214041253 : Nat.Prime 1214041253 := by
  apply lucas_primality 1214041253 (2 : ZMod 1214041253)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (15974227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (15974227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1214041253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_15974227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1214041253) ^ 607020626 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1214041253) ^ 63896908 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1214041253) ^ 76 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1452663529 : Nat.Prime 1452663529 := by
  apply lucas_primality 1452663529 (13 : ZMod 1452663529)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (167, 1), (293, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (167, 1), (293, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452663529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_167
      · exact prime_oneHundredElevenDE_293
      · exact prime_oneHundredElevenDE_1237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1452663529) ^ 726331764 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1452663529) ^ 484221176 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1452663529) ^ 8698584 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1452663529) ^ 4957896 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1452663529) ^ 1174344 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1542673981 : Nat.Prime 1542673981 := by
  apply lucas_primality 1542673981 (10 : ZMod 1542673981)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (8570411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (8570411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1542673981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_8570411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1542673981) ^ 771336990 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1542673981) ^ 514224660 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1542673981) ^ 308534796 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1542673981) ^ 180 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1610475287 : Nat.Prime 1610475287 := by
  apply lucas_primality 1610475287 (5 : ZMod 1610475287)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (97, 1), (1087, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (97, 1), (1087, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1610475287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_97
      · exact prime_oneHundredElevenDE_1087
      · exact prime_oneHundredElevenDE_1091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1610475287) ^ 805237643 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1610475287) ^ 230067898 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1610475287) ^ 16602838 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1610475287) ^ 1481578 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1610475287) ^ 1476146 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1791551689 : Nat.Prime 1791551689 := by
  apply lucas_primality 1791551689 (13 : ZMod 1791551689)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (733, 1), (101839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (733, 1), (101839, 1)] : List FactorBlock).map factorBlockValue).prod) = 1791551689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_733
      · exact prime_oneHundredElevenDE_101839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1791551689) ^ 895775844 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1791551689) ^ 597183896 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1791551689) ^ 2444136 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1791551689) ^ 17592 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1948013029 : Nat.Prime 1948013029 := by
  apply lucas_primality 1948013029 (6 : ZMod 1948013029)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (4162421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (4162421, 1)] : List FactorBlock).map factorBlockValue).prod) = 1948013029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_4162421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1948013029) ^ 974006514 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1948013029) ^ 649337676 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1948013029) ^ 149847156 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1948013029) ^ 468 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2389640179 : Nat.Prime 2389640179 := by
  apply lucas_primality 2389640179 (2 : ZMod 2389640179)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (398273363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (398273363, 1)] : List FactorBlock).map factorBlockValue).prod) = 2389640179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_398273363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2389640179) ^ 1194820089 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2389640179) ^ 796546726 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2389640179) ^ 6 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2769784141 : Nat.Prime 2769784141 := by
  apply lucas_primality 2769784141 (2 : ZMod 2769784141)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (46163069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (46163069, 1)] : List FactorBlock).map factorBlockValue).prod) = 2769784141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_46163069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2769784141) ^ 1384892070 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769784141) ^ 923261380 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769784141) ^ 553956828 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769784141) ^ 60 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2834972519 : Nat.Prime 2834972519 := by
  apply lucas_primality 2834972519 (7 : ZMod 2834972519)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (1693, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (1693, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) = 2834972519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_1693
      · exact prime_oneHundredElevenDE_2441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2834972519) ^ 1417486259 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2834972519) ^ 404996074 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2834972519) ^ 1674526 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2834972519) ^ 1161398 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_3372155771 : Nat.Prime 3372155771 := by
  apply lucas_primality 3372155771 (2 : ZMod 3372155771)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (337215577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (337215577, 1)] : List FactorBlock).map factorBlockValue).prod) = 3372155771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_337215577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3372155771) ^ 1686077885 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3372155771) ^ 674431154 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3372155771) ^ 10 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_3421583713 : Nat.Prime 3421583713 := by
  apply lucas_primality 3421583713 (10 : ZMod 3421583713)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (199, 1), (227, 1), (263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (199, 1), (227, 1), (263, 1)] : List FactorBlock).map factorBlockValue).prod) = 3421583713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_199
      · exact prime_oneHundredElevenDE_227
      · exact prime_oneHundredElevenDE_263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3421583713) ^ 1710791856 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 3421583713) ^ 1140527904 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 3421583713) ^ 17193888 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 3421583713) ^ 15073056 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 3421583713) ^ 13009824 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_4072639631 : Nat.Prime 4072639631 := by
  apply lucas_primality 4072639631 (7 : ZMod 4072639631)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (407263963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (407263963, 1)] : List FactorBlock).map factorBlockValue).prod) = 4072639631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_407263963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4072639631) ^ 2036319815 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4072639631) ^ 814527926 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4072639631) ^ 10 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_5210386787 : Nat.Prime 5210386787 := by
  apply lucas_primality 5210386787 (2 : ZMod 5210386787)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3613, 1), (65551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3613, 1), (65551, 1)] : List FactorBlock).map factorBlockValue).prod) = 5210386787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_3613
      · exact prime_oneHundredElevenDE_65551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5210386787) ^ 2605193393 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5210386787) ^ 473671526 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5210386787) ^ 1442122 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5210386787) ^ 79486 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_5692305809 : Nat.Prime 5692305809 := by
  apply lucas_primality 5692305809 (6 : ZMod 5692305809)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (31, 1), (509, 1), (3221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (31, 1), (509, 1), (3221, 1)] : List FactorBlock).map factorBlockValue).prod) = 5692305809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_509
      · exact prime_oneHundredElevenDE_3221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5692305809) ^ 2846152904 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5692305809) ^ 813186544 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5692305809) ^ 183622768 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5692305809) ^ 11183312 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5692305809) ^ 1767248 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_6293333183 : Nat.Prime 6293333183 := by
  apply lucas_primality 6293333183 (5 : ZMod 6293333183)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (47, 1), (67, 1), (113, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (47, 1), (67, 1), (113, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 6293333183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_37
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_67
      · exact prime_oneHundredElevenDE_113
      · exact prime_oneHundredElevenDE_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6293333183) ^ 3146666591 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 170090086 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 133900706 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 93930346 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 55693214 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 26331938 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_6439451269 : Nat.Prime 6439451269 := by
  apply lucas_primality 6439451269 (7 : ZMod 6439451269)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (163, 1), (337, 1), (9769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (163, 1), (337, 1), (9769, 1)] : List FactorBlock).map factorBlockValue).prod) = 6439451269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_163
      · exact prime_oneHundredElevenDE_337
      · exact prime_oneHundredElevenDE_9769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6439451269) ^ 3219725634 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6439451269) ^ 2146483756 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6439451269) ^ 39505836 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6439451269) ^ 19108164 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6439451269) ^ 659172 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_6682494491 : Nat.Prime 6682494491 := by
  apply lucas_primality 6682494491 (2 : ZMod 6682494491)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (61, 1), (211, 1), (7417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (61, 1), (211, 1), (7417, 1)] : List FactorBlock).map factorBlockValue).prod) = 6682494491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_211
      · exact prime_oneHundredElevenDE_7417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6682494491) ^ 3341247245 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6682494491) ^ 1336498898 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6682494491) ^ 954642070 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6682494491) ^ 109549090 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6682494491) ^ 31670590 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6682494491) ^ 900970 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_6811701929 : Nat.Prime 6811701929 := by
  apply lucas_primality 6811701929 (3 : ZMod 6811701929)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (269, 1), (3165289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (269, 1), (3165289, 1)] : List FactorBlock).map factorBlockValue).prod) = 6811701929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_269
      · exact prime_oneHundredElevenDE_3165289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6811701929) ^ 3405850964 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6811701929) ^ 25322312 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6811701929) ^ 2152 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_7794858109 : Nat.Prime 7794858109 := by
  apply lucas_primality 7794858109 (2 : ZMod 7794858109)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (649571509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (649571509, 1)] : List FactorBlock).map factorBlockValue).prod) = 7794858109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_649571509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7794858109) ^ 3897429054 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7794858109) ^ 2598286036 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7794858109) ^ 12 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_11238561589 : Nat.Prime 11238561589 := by
  apply lucas_primality 11238561589 (2 : ZMod 11238561589)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7121, 1), (131519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7121, 1), (131519, 1)] : List FactorBlock).map factorBlockValue).prod) = 11238561589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7121
      · exact prime_oneHundredElevenDE_131519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11238561589) ^ 5619280794 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11238561589) ^ 3746187196 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11238561589) ^ 1578228 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11238561589) ^ 85452 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_11384611619 : Nat.Prime 11384611619 := by
  apply lucas_primality 11384611619 (2 : ZMod 11384611619)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5692305809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5692305809, 1)] : List FactorBlock).map factorBlockValue).prod) = 11384611619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5692305809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11384611619) ^ 5692305809 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11384611619) ^ 2 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_12112361333 : Nat.Prime 12112361333 := by
  apply lucas_primality 12112361333 (2 : ZMod 12112361333)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (22277, 1), (135929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (22277, 1), (135929, 1)] : List FactorBlock).map factorBlockValue).prod) = 12112361333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_22277
      · exact prime_oneHundredElevenDE_135929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12112361333) ^ 6056180666 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12112361333) ^ 543716 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12112361333) ^ 89108 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_14096978603 : Nat.Prime 14096978603 := by
  apply lucas_primality 14096978603 (2 : ZMod 14096978603)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (761, 1), (14867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (761, 1), (14867, 1)] : List FactorBlock).map factorBlockValue).prod) = 14096978603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_89
      · exact prime_oneHundredElevenDE_761
      · exact prime_oneHundredElevenDE_14867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14096978603) ^ 7048489301 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14096978603) ^ 2013854086 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14096978603) ^ 158393018 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14096978603) ^ 18524282 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14096978603) ^ 948206 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_14099086907 : Nat.Prime 14099086907 := by
  apply lucas_primality 14099086907 (2 : ZMod 14099086907)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (163942871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (163942871, 1)] : List FactorBlock).map factorBlockValue).prod) = 14099086907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_43
      · exact prime_oneHundredElevenDE_163942871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14099086907) ^ 7049543453 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14099086907) ^ 327885742 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14099086907) ^ 86 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_16462091119 : Nat.Prime 16462091119 := by
  apply lucas_primality 16462091119 (6 : ZMod 16462091119)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (249425623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (249425623, 1)] : List FactorBlock).map factorBlockValue).prod) = 16462091119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_249425623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 16462091119) ^ 8231045559 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 16462091119) ^ 5487363706 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 16462091119) ^ 1496553738 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 16462091119) ^ 66 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_19171536113 : Nat.Prime 19171536113 := by
  apply lucas_primality 19171536113 (3 : ZMod 19171536113)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (193, 1), (379, 1), (16381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (193, 1), (379, 1), (16381, 1)] : List FactorBlock).map factorBlockValue).prod) = 19171536113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_193
      · exact prime_oneHundredElevenDE_379
      · exact prime_oneHundredElevenDE_16381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19171536113) ^ 9585768056 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19171536113) ^ 99334384 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19171536113) ^ 50584528 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19171536113) ^ 1170352 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_19653905023 : Nat.Prime 19653905023 := by
  apply lucas_primality 19653905023 (3 : ZMod 19653905023)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (4289, 1), (11399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (4289, 1), (11399, 1)] : List FactorBlock).map factorBlockValue).prod) = 19653905023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_67
      · exact prime_oneHundredElevenDE_4289
      · exact prime_oneHundredElevenDE_11399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19653905023) ^ 9826952511 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19653905023) ^ 6551301674 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19653905023) ^ 293341866 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19653905023) ^ 4582398 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 19653905023) ^ 1724178 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_22679780153 : Nat.Prime 22679780153 := by
  apply lucas_primality 22679780153 (3 : ZMod 22679780153)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2834972519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2834972519, 1)] : List FactorBlock).map factorBlockValue).prod) = 22679780153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_2834972519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 22679780153) ^ 11339890076 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 22679780153) ^ 8 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_28464725449 : Nat.Prime 28464725449 := by
  apply lucas_primality 28464725449 (11 : ZMod 28464725449)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37, 1), (353, 1), (30269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37, 1), (353, 1), (30269, 1)] : List FactorBlock).map factorBlockValue).prod) = 28464725449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_37
      · exact prime_oneHundredElevenDE_353
      · exact prime_oneHundredElevenDE_30269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 28464725449) ^ 14232362724 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 28464725449) ^ 9488241816 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 28464725449) ^ 769316904 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 28464725449) ^ 80636616 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 28464725449) ^ 940392 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_28859270599 : Nat.Prime 28859270599 := by
  apply lucas_primality 28859270599 (3 : ZMod 28859270599)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (29, 1), (47, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (29, 1), (47, 1), (392099, 1)] : List FactorBlock).map factorBlockValue).prod) = 28859270599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_29
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_392099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28859270599) ^ 14429635299 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 28859270599) ^ 9619756866 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 28859270599) ^ 995147262 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 28859270599) ^ 614027034 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 28859270599) ^ 73602 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_33411929623 : Nat.Prime 33411929623 := by
  apply lucas_primality 33411929623 (3 : ZMod 33411929623)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (1283, 1), (54941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (1283, 1), (54941, 1)] : List FactorBlock).map factorBlockValue).prod) = 33411929623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_79
      · exact prime_oneHundredElevenDE_1283
      · exact prime_oneHundredElevenDE_54941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33411929623) ^ 16705964811 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 33411929623) ^ 11137309874 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 33411929623) ^ 422935818 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 33411929623) ^ 26042034 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 33411929623) ^ 608142 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_34525458431 : Nat.Prime 34525458431 := by
  apply lucas_primality 34525458431 (14 : ZMod 34525458431)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17291, 1), (199673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17291, 1), (199673, 1)] : List FactorBlock).map factorBlockValue).prod) = 34525458431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_17291
      · exact prime_oneHundredElevenDE_199673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 34525458431) ^ 17262729215 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 34525458431) ^ 6905091686 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 34525458431) ^ 1996730 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 34525458431) ^ 172910 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_36421237591 : Nat.Prime 36421237591 := by
  apply lucas_primality 36421237591 (3 : ZMod 36421237591)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1214041253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1214041253, 1)] : List FactorBlock).map factorBlockValue).prod) = 36421237591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_1214041253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 36421237591) ^ 18210618795 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 36421237591) ^ 12140412530 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 36421237591) ^ 7284247518 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 36421237591) ^ 30 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_37727210827 : Nat.Prime 37727210827 := by
  apply lucas_primality 37727210827 (2 : ZMod 37727210827)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (199, 1), (172663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (199, 1), (172663, 1)] : List FactorBlock).map factorBlockValue).prod) = 37727210827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_199
      · exact prime_oneHundredElevenDE_172663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37727210827) ^ 18863605413 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37727210827) ^ 12575736942 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37727210827) ^ 618478866 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37727210827) ^ 189583974 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37727210827) ^ 218502 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_41136350837 : Nat.Prime 41136350837 := by
  apply lucas_primality 41136350837 (2 : ZMod 41136350837)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (1933, 1), (15511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (1933, 1), (15511, 1)] : List FactorBlock).map factorBlockValue).prod) = 41136350837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_1933
      · exact prime_oneHundredElevenDE_15511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41136350837) ^ 20568175418 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41136350837) ^ 5876621548 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41136350837) ^ 21281092 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41136350837) ^ 2652076 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_41326142149 : Nat.Prime 41326142149 := by
  apply lucas_primality 41326142149 (2 : ZMod 41326142149)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1531, 1), (749803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1531, 1), (749803, 1)] : List FactorBlock).map factorBlockValue).prod) = 41326142149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_1531
      · exact prime_oneHundredElevenDE_749803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41326142149) ^ 20663071074 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41326142149) ^ 13775380716 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41326142149) ^ 26992908 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41326142149) ^ 55116 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_54702140897 : Nat.Prime 54702140897 := by
  apply lucas_primality 54702140897 (3 : ZMod 54702140897)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (23, 1), (397, 1), (14401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (23, 1), (397, 1), (14401, 1)] : List FactorBlock).map factorBlockValue).prod) = 54702140897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_397
      · exact prime_oneHundredElevenDE_14401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54702140897) ^ 27351070448 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 54702140897) ^ 4207856992 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 54702140897) ^ 2378353952 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 54702140897) ^ 137788768 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 54702140897) ^ 3798496 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_66389767537 : Nat.Prime 66389767537 := by
  apply lucas_primality 66389767537 (13 : ZMod 66389767537)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (1327, 1), (45317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (1327, 1), (45317, 1)] : List FactorBlock).map factorBlockValue).prod) = 66389767537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_1327
      · exact prime_oneHundredElevenDE_45317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 66389767537) ^ 33194883768 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 66389767537) ^ 22129922512 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 66389767537) ^ 2886511632 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 66389767537) ^ 50029968 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 66389767537) ^ 1465008 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_75734237339 : Nat.Prime 75734237339 := by
  apply lucas_primality 75734237339 (2 : ZMod 75734237339)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (518727653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (518727653, 1)] : List FactorBlock).map factorBlockValue).prod) = 75734237339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_73
      · exact prime_oneHundredElevenDE_518727653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75734237339) ^ 37867118669 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 75734237339) ^ 1037455306 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 75734237339) ^ 146 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_81919066609 : Nat.Prime 81919066609 := by
  apply lucas_primality 81919066609 (23 : ZMod 81919066609)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (17, 1), (47, 1), (237331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (17, 1), (47, 1), (237331, 1)] : List FactorBlock).map factorBlockValue).prod) = 81919066609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_237331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 81919066609) ^ 40959533304 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (23 : ZMod 81919066609) ^ 27306355536 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (23 : ZMod 81919066609) ^ 4818768624 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (23 : ZMod 81919066609) ^ 1742958864 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (23 : ZMod 81919066609) ^ 345168 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_91092127657 : Nat.Prime 91092127657 := by
  apply lucas_primality 91092127657 (7 : ZMod 91092127657)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (521, 1), (1481, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (521, 1), (1481, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) = 91092127657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_521
      · exact prime_oneHundredElevenDE_1481
      · exact prime_oneHundredElevenDE_4919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 91092127657) ^ 45546063828 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 91092127657) ^ 30364042552 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 91092127657) ^ 174840936 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 91092127657) ^ 61507176 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 91092127657) ^ 18518424 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_91610802659 : Nat.Prime 91610802659 := by
  apply lucas_primality 91610802659 (2 : ZMod 91610802659)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (974583007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (974583007, 1)] : List FactorBlock).map factorBlockValue).prod) = 91610802659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_974583007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 91610802659) ^ 45805401329 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 91610802659) ^ 1949166014 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 91610802659) ^ 94 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_121231121951 : Nat.Prime 121231121951 := by
  apply lucas_primality 121231121951 (7 : ZMod 121231121951)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2243, 1), (1080973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2243, 1), (1080973, 1)] : List FactorBlock).map factorBlockValue).prod) = 121231121951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_2243
      · exact prime_oneHundredElevenDE_1080973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 121231121951) ^ 60615560975 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 121231121951) ^ 24246224390 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 121231121951) ^ 54048650 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 121231121951) ^ 112150 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_162323369267 : Nat.Prime 162323369267 := by
  apply lucas_primality 162323369267 (2 : ZMod 162323369267)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6329, 1), (12823777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6329, 1), (12823777, 1)] : List FactorBlock).map factorBlockValue).prod) = 162323369267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_6329
      · exact prime_oneHundredElevenDE_12823777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 162323369267) ^ 81161684633 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 162323369267) ^ 25647554 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 162323369267) ^ 12658 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_177403671667 : Nat.Prime 177403671667 := by
  apply lucas_primality 177403671667 (3 : ZMod 177403671667)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (13, 1), (17, 1), (31, 1), (53281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (13, 1), (17, 1), (31, 1), (53281, 1)] : List FactorBlock).map factorBlockValue).prod) = 177403671667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_53281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 177403671667) ^ 88701835833 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177403671667) ^ 59134557222 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177403671667) ^ 13646436282 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177403671667) ^ 10435510098 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177403671667) ^ 5722699086 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177403671667) ^ 3329586 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_200471577739 : Nat.Prime 200471577739 := by
  apply lucas_primality 200471577739 (3 : ZMod 200471577739)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (33411929623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (33411929623, 1)] : List FactorBlock).map factorBlockValue).prod) = 200471577739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_33411929623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 200471577739) ^ 100235788869 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 200471577739) ^ 66823859246 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 200471577739) ^ 6 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_223794433691 : Nat.Prime 223794433691 := by
  apply lucas_primality 223794433691 (2 : ZMod 223794433691)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21773, 1), (1027853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21773, 1), (1027853, 1)] : List FactorBlock).map factorBlockValue).prod) = 223794433691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_21773
      · exact prime_oneHundredElevenDE_1027853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 223794433691) ^ 111897216845 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 223794433691) ^ 44758886738 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 223794433691) ^ 10278530 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 223794433691) ^ 217730 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_237319406381 : Nat.Prime 237319406381 := by
  apply lucas_primality 237319406381 (2 : ZMod 237319406381)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (23, 1), (59, 1), (227, 1), (5503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (23, 1), (59, 1), (227, 1), (5503, 1)] : List FactorBlock).map factorBlockValue).prod) = 237319406381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_59
      · exact prime_oneHundredElevenDE_227
      · exact prime_oneHundredElevenDE_5503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237319406381) ^ 118659703190 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 237319406381) ^ 47463881276 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 237319406381) ^ 33902772340 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 237319406381) ^ 10318235060 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 237319406381) ^ 4022362820 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 237319406381) ^ 1045459940 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 237319406381) ^ 43125460 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_254482680649 : Nat.Prime 254482680649 := by
  apply lucas_primality 254482680649 (33 : ZMod 254482680649)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (1951, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (1951, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) = 254482680649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_1951
      · exact prime_oneHundredElevenDE_33757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 254482680649) ^ 127241340324 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 84827560216 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 36354668664 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 11064464376 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 130437048 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 7538664 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_260519339351 : Nat.Prime 260519339351 := by
  apply lucas_primality 260519339351 (17 : ZMod 260519339351)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (5210386787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (5210386787, 1)] : List FactorBlock).map factorBlockValue).prod) = 260519339351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_5210386787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 260519339351) ^ 130259669675 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (17 : ZMod 260519339351) ^ 52103867870 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (17 : ZMod 260519339351) ^ 50 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_299483516401 : Nat.Prime 299483516401 := by
  apply lucas_primality 299483516401 (14 : ZMod 299483516401)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (249569597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (249569597, 1)] : List FactorBlock).map factorBlockValue).prod) = 299483516401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_249569597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 299483516401) ^ 149741758200 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 299483516401) ^ 99827838800 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 299483516401) ^ 59896703280 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 299483516401) ^ 1200 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_317516922143 : Nat.Prime 317516922143 := by
  apply lucas_primality 317516922143 (5 : ZMod 317516922143)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (22679780153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (22679780153, 1)] : List FactorBlock).map factorBlockValue).prod) = 317516922143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_22679780153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 317516922143) ^ 158758461071 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 317516922143) ^ 45359560306 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 317516922143) ^ 14 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_324437051129 : Nat.Prime 324437051129 := by
  apply lucas_primality 324437051129 (3 : ZMod 324437051129)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (1039, 1), (952009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (1039, 1), (952009, 1)] : List FactorBlock).map factorBlockValue).prod) = 324437051129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_1039
      · exact prime_oneHundredElevenDE_952009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 324437051129) ^ 162218525564 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 324437051129) ^ 7913098808 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 324437051129) ^ 312258952 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 324437051129) ^ 340792 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_347586660433 : Nat.Prime 347586660433 := by
  apply lucas_primality 347586660433 (7 : ZMod 347586660433)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (11, 1), (73145341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (11, 1), (73145341, 1)] : List FactorBlock).map factorBlockValue).prod) = 347586660433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_73145341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 347586660433) ^ 173793330216 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 347586660433) ^ 115862220144 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 347586660433) ^ 31598787312 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 347586660433) ^ 4752 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_351083612567 : Nat.Prime 351083612567 := by
  apply lucas_primality 351083612567 (5 : ZMod 351083612567)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (1610475287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (1610475287, 1)] : List FactorBlock).map factorBlockValue).prod) = 351083612567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_109
      · exact prime_oneHundredElevenDE_1610475287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 351083612567) ^ 175541806283 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 351083612567) ^ 3220950574 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 351083612567) ^ 218 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_453218926397 : Nat.Prime 453218926397 := by
  apply lucas_primality 453218926397 (2 : ZMod 453218926397)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (67, 1), (1399, 1), (29483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (67, 1), (1399, 1), (29483, 1)] : List FactorBlock).map factorBlockValue).prod) = 453218926397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_67
      · exact prime_oneHundredElevenDE_1399
      · exact prime_oneHundredElevenDE_29483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 453218926397) ^ 226609463198 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 453218926397) ^ 11054120156 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 453218926397) ^ 6764461588 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 453218926397) ^ 323959204 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 453218926397) ^ 15372212 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_468859333643 : Nat.Prime 468859333643 := by
  apply lucas_primality 468859333643 (2 : ZMod 468859333643)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1307, 1), (2273, 1), (11273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1307, 1), (2273, 1), (11273, 1)] : List FactorBlock).map factorBlockValue).prod) = 468859333643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_1307
      · exact prime_oneHundredElevenDE_2273
      · exact prime_oneHundredElevenDE_11273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 468859333643) ^ 234429666821 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 468859333643) ^ 66979904806 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 468859333643) ^ 358729406 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 468859333643) ^ 206273354 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 468859333643) ^ 41591354 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_584409528191 : Nat.Prime 584409528191 := by
  apply lucas_primality 584409528191 (11 : ZMod 584409528191)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (223, 1), (577, 1), (26717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (223, 1), (577, 1), (26717, 1)] : List FactorBlock).map factorBlockValue).prod) = 584409528191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_223
      · exact prime_oneHundredElevenDE_577
      · exact prime_oneHundredElevenDE_26717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 584409528191) ^ 292204764095 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 116881905638 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 34377031070 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 2620670530 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 1012841470 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 21874070 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_969848975609 : Nat.Prime 969848975609 := by
  apply lucas_primality 969848975609 (3 : ZMod 969848975609)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (121231121951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (121231121951, 1)] : List FactorBlock).map factorBlockValue).prod) = 969848975609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_121231121951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 969848975609) ^ 484924487804 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 969848975609) ^ 8 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_982510607471 : Nat.Prime 982510607471 := by
  apply lucas_primality 982510607471 (14 : ZMod 982510607471)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (47, 1), (53, 1), (61, 1), (71, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (47, 1), (53, 1), (61, 1), (71, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) = 982510607471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_53
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_71
      · exact prime_oneHundredElevenDE_1301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 982510607471) ^ 491255303735 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 982510607471) ^ 196502121494 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 982510607471) ^ 140358658210 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 982510607471) ^ 20904481010 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 982510607471) ^ 18537935990 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 982510607471) ^ 16106731270 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 982510607471) ^ 13838177570 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 982510607471) ^ 755196470 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1231858315333 : Nat.Prime 1231858315333 := by
  apply lucas_primality 1231858315333 (5 : ZMod 1231858315333)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (61, 1), (439, 1), (1277803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (61, 1), (439, 1), (1277803, 1)] : List FactorBlock).map factorBlockValue).prod) = 1231858315333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_439
      · exact prime_oneHundredElevenDE_1277803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1231858315333) ^ 615929157666 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231858315333) ^ 410619438444 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231858315333) ^ 20194398612 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231858315333) ^ 2806055388 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231858315333) ^ 964044 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1324030981249 : Nat.Prime 1324030981249 := by
  apply lucas_primality 1324030981249 (13 : ZMod 1324030981249)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (59, 1), (1039, 1), (18749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (59, 1), (1039, 1), (18749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1324030981249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_59
      · exact prime_oneHundredElevenDE_1039
      · exact prime_oneHundredElevenDE_18749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1324030981249) ^ 662015490624 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1324030981249) ^ 441343660416 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1324030981249) ^ 22441203072 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1324030981249) ^ 1274332032 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 1324030981249) ^ 70618752 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1563116036107 : Nat.Prime 1563116036107 := by
  apply lucas_primality 1563116036107 (2 : ZMod 1563116036107)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (260519339351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (260519339351, 1)] : List FactorBlock).map factorBlockValue).prod) = 1563116036107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_260519339351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1563116036107) ^ 781558018053 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563116036107) ^ 521038678702 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563116036107) ^ 6 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1772374521901 : Nat.Prime 1772374521901 := by
  apply lucas_primality 1772374521901 (2 : ZMod 1772374521901)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (16187, 1), (364979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (16187, 1), (364979, 1)] : List FactorBlock).map factorBlockValue).prod) = 1772374521901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_16187
      · exact prime_oneHundredElevenDE_364979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1772374521901) ^ 886187260950 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1772374521901) ^ 590791507300 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1772374521901) ^ 354474904380 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1772374521901) ^ 109493700 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1772374521901) ^ 4856100 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1776175990993 : Nat.Prime 1776175990993 := by
  apply lucas_primality 1776175990993 (10 : ZMod 1776175990993)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (1223, 1), (775807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (1223, 1), (775807, 1)] : List FactorBlock).map factorBlockValue).prod) = 1776175990993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_1223
      · exact prime_oneHundredElevenDE_775807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1776175990993) ^ 888087995496 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1776175990993) ^ 592058663664 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1776175990993) ^ 136628922384 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1776175990993) ^ 1452310704 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 1776175990993) ^ 2289456 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2039319279281 : Nat.Prime 2039319279281 := by
  apply lucas_primality 2039319279281 (13 : ZMod 2039319279281)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (31, 1), (822306161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (31, 1), (822306161, 1)] : List FactorBlock).map factorBlockValue).prod) = 2039319279281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_822306161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2039319279281) ^ 1019659639640 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2039319279281) ^ 407863855856 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2039319279281) ^ 65784492880 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2039319279281) ^ 2480 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2344392986017 : Nat.Prime 2344392986017 := by
  apply lucas_primality 2344392986017 (7 : ZMod 2344392986017)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (997, 1), (24494243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (997, 1), (24494243, 1)] : List FactorBlock).map factorBlockValue).prod) = 2344392986017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_997
      · exact prime_oneHundredElevenDE_24494243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2344392986017) ^ 1172196493008 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2344392986017) ^ 781464328672 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2344392986017) ^ 2351447328 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2344392986017) ^ 95712 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2562585990521 : Nat.Prime 2562585990521 := by
  apply lucas_primality 2562585990521 (6 : ZMod 2562585990521)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (11353, 1), (55871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (11353, 1), (55871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2562585990521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_101
      · exact prime_oneHundredElevenDE_11353
      · exact prime_oneHundredElevenDE_55871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2562585990521) ^ 1281292995260 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2562585990521) ^ 512517198104 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2562585990521) ^ 25372138520 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2562585990521) ^ 225718840 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2562585990521) ^ 45866120 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2881165199599 : Nat.Prime 2881165199599 := by
  apply lucas_primality 2881165199599 (3 : ZMod 2881165199599)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (103, 1), (222003791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (103, 1), (222003791, 1)] : List FactorBlock).map factorBlockValue).prod) = 2881165199599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_103
      · exact prime_oneHundredElevenDE_222003791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2881165199599) ^ 1440582599799 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2881165199599) ^ 960388399866 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2881165199599) ^ 411595028514 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2881165199599) ^ 27972477666 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2881165199599) ^ 12978 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_3066433510013 : Nat.Prime 3066433510013 := by
  apply lucas_primality 3066433510013 (2 : ZMod 3066433510013)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (154667, 1), (4956509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (154667, 1), (4956509, 1)] : List FactorBlock).map factorBlockValue).prod) = 3066433510013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_154667
      · exact prime_oneHundredElevenDE_4956509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3066433510013) ^ 1533216755006 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3066433510013) ^ 19826036 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3066433510013) ^ 618668 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_3493681386313 : Nat.Prime 3493681386313 := by
  apply lucas_primality 3493681386313 (5 : ZMod 3493681386313)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (3643, 1), (3073757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (3643, 1), (3073757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3493681386313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_3643
      · exact prime_oneHundredElevenDE_3073757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3493681386313) ^ 1746840693156 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3493681386313) ^ 1164560462104 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3493681386313) ^ 268744722024 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3493681386313) ^ 959012184 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3493681386313) ^ 1136616 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_4016750233037 : Nat.Prime 4016750233037 := by
  apply lucas_primality 4016750233037 (2 : ZMod 4016750233037)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (16462091119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (16462091119, 1)] : List FactorBlock).map factorBlockValue).prod) = 4016750233037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_16462091119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4016750233037) ^ 2008375116518 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4016750233037) ^ 65848364476 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4016750233037) ^ 244 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_4078638558563 : Nat.Prime 4078638558563 := by
  apply lucas_primality 4078638558563 (2 : ZMod 4078638558563)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2039319279281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2039319279281, 1)] : List FactorBlock).map factorBlockValue).prod) = 4078638558563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_2039319279281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4078638558563) ^ 2039319279281 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4078638558563) ^ 2 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_4121229406079 : Nat.Prime 4121229406079 := by
  apply lucas_primality 4121229406079 (7 : ZMod 4121229406079)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (11384611619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (11384611619, 1)] : List FactorBlock).map factorBlockValue).prod) = 4121229406079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_181
      · exact prime_oneHundredElevenDE_11384611619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4121229406079) ^ 2060614703039 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4121229406079) ^ 22769223238 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 4121229406079) ^ 362 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_5155122637909 : Nat.Prime 5155122637909 := by
  apply lucas_primality 5155122637909 (2 : ZMod 5155122637909)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (6907, 1), (309437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (6907, 1), (309437, 1)] : List FactorBlock).map factorBlockValue).prod) = 5155122637909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_67
      · exact prime_oneHundredElevenDE_6907
      · exact prime_oneHundredElevenDE_309437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5155122637909) ^ 2577561318954 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155122637909) ^ 1718374212636 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155122637909) ^ 76942128924 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155122637909) ^ 746362044 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155122637909) ^ 16659684 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_6967549835189 : Nat.Prime 6967549835189 := by
  apply lucas_primality 6967549835189 (2 : ZMod 6967549835189)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (75734237339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (75734237339, 1)] : List FactorBlock).map factorBlockValue).prod) = 6967549835189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_75734237339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6967549835189) ^ 3483774917594 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6967549835189) ^ 302936949356 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6967549835189) ^ 92 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_9566758866199 : Nat.Prime 9566758866199 := by
  apply lucas_primality 9566758866199 (3 : ZMod 9566758866199)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (695749, 1), (2291717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (695749, 1), (2291717, 1)] : List FactorBlock).map factorBlockValue).prod) = 9566758866199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_695749
      · exact prime_oneHundredElevenDE_2291717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9566758866199) ^ 4783379433099 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 9566758866199) ^ 3188919622066 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 9566758866199) ^ 13750302 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 9566758866199) ^ 4174494 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_10008199097573 : Nat.Prime 10008199097573 := by
  apply lucas_primality 10008199097573 (2 : ZMod 10008199097573)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (3433, 1), (56063317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (3433, 1), (56063317, 1)] : List FactorBlock).map factorBlockValue).prod) = 10008199097573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_3433
      · exact prime_oneHundredElevenDE_56063317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10008199097573) ^ 5004099548786 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10008199097573) ^ 769861469044 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10008199097573) ^ 2915292484 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10008199097573) ^ 178516 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_10778453111597 : Nat.Prime 10778453111597 := by
  apply lucas_primality 10778453111597 (2 : ZMod 10778453111597)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (349, 1), (2861, 1), (2698691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (349, 1), (2861, 1), (2698691, 1)] : List FactorBlock).map factorBlockValue).prod) = 10778453111597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_349
      · exact prime_oneHundredElevenDE_2861
      · exact prime_oneHundredElevenDE_2698691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10778453111597) ^ 5389226555798 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10778453111597) ^ 30883819804 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10778453111597) ^ 3767372636 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10778453111597) ^ 3993956 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_11485426273469 : Nat.Prime 11485426273469 := by
  apply lucas_primality 11485426273469 (2 : ZMod 11485426273469)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (23, 1), (3719, 1), (282089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (23, 1), (3719, 1), (282089, 1)] : List FactorBlock).map factorBlockValue).prod) = 11485426273469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_3719
      · exact prime_oneHundredElevenDE_282089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11485426273469) ^ 5742713136734 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11485426273469) ^ 1640775181924 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11485426273469) ^ 675613310204 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11485426273469) ^ 499366359716 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11485426273469) ^ 3088310372 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11485426273469) ^ 40715612 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_14090079456749 : Nat.Prime 14090079456749 := by
  apply lucas_primality 14090079456749 (2 : ZMod 14090079456749)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (81919066609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (81919066609, 1)] : List FactorBlock).map factorBlockValue).prod) = 14090079456749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_43
      · exact prime_oneHundredElevenDE_81919066609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14090079456749) ^ 7045039728374 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14090079456749) ^ 327676266436 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14090079456749) ^ 172 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_14344123360423 : Nat.Prime 14344123360423 := by
  apply lucas_primality 14344123360423 (3 : ZMod 14344123360423)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (22391, 1), (1199663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (22391, 1), (1199663, 1)] : List FactorBlock).map factorBlockValue).prod) = 14344123360423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_89
      · exact prime_oneHundredElevenDE_22391
      · exact prime_oneHundredElevenDE_1199663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14344123360423) ^ 7172061680211 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344123360423) ^ 4781374453474 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344123360423) ^ 161169925398 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344123360423) ^ 640620042 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344123360423) ^ 11956794 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_15011284666871 : Nat.Prime 15011284666871 := by
  apply lucas_primality 15011284666871 (11 : ZMod 15011284666871)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (1997, 1), (44217163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (1997, 1), (44217163, 1)] : List FactorBlock).map factorBlockValue).prod) = 15011284666871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_1997
      · exact prime_oneHundredElevenDE_44217163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 15011284666871) ^ 7505642333435 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 15011284666871) ^ 3002256933374 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 15011284666871) ^ 883016745110 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 15011284666871) ^ 7516917710 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 15011284666871) ^ 339490 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_18293785381727 : Nat.Prime 18293785381727 := by
  apply lucas_primality 18293785381727 (5 : ZMod 18293785381727)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (271, 1), (821, 1), (41111293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (271, 1), (821, 1), (41111293, 1)] : List FactorBlock).map factorBlockValue).prod) = 18293785381727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_271
      · exact prime_oneHundredElevenDE_821
      · exact prime_oneHundredElevenDE_41111293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18293785381727) ^ 9146892690863 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 18293785381727) ^ 67504743106 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 18293785381727) ^ 22282320806 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 18293785381727) ^ 444982 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_22986283483379 : Nat.Prime 22986283483379 := by
  apply lucas_primality 22986283483379 (2 : ZMod 22986283483379)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (59, 1), (97, 1), (113, 1), (461, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (59, 1), (97, 1), (113, 1), (461, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) = 22986283483379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_59
      · exact prime_oneHundredElevenDE_97
      · exact prime_oneHundredElevenDE_113
      · exact prime_oneHundredElevenDE_461
      · exact prime_oneHundredElevenDE_2029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22986283483379) ^ 11493141741689 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 1209804393862 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 389598025142 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 236971994674 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 203418437906 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 49861786298 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 11328873082 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_26541986175517 : Nat.Prime 26541986175517 := by
  apply lucas_primality 26541986175517 (2 : ZMod 26541986175517)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (31, 1), (41, 1), (359, 1), (23879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (31, 1), (41, 1), (359, 1), (23879, 1)] : List FactorBlock).map factorBlockValue).prod) = 26541986175517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_29
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_359
      · exact prime_oneHundredElevenDE_23879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26541986175517) ^ 13270993087758 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26541986175517) ^ 8847328725172 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26541986175517) ^ 3791712310788 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26541986175517) ^ 915240902604 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26541986175517) ^ 856193102436 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26541986175517) ^ 647365516476 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26541986175517) ^ 73933109124 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26541986175517) ^ 1111520004 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_37142849712461 : Nat.Prime 37142849712461 := by
  apply lucas_primality 37142849712461 (2 : ZMod 37142849712461)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13417, 1), (138417119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13417, 1), (138417119, 1)] : List FactorBlock).map factorBlockValue).prod) = 37142849712461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_13417
      · exact prime_oneHundredElevenDE_138417119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37142849712461) ^ 18571424856230 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37142849712461) ^ 7428569942492 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37142849712461) ^ 2768342380 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37142849712461) ^ 268340 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_52819074474709 : Nat.Prime 52819074474709 := by
  apply lucas_primality 52819074474709 (2 : ZMod 52819074474709)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (41136350837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (41136350837, 1)] : List FactorBlock).map factorBlockValue).prod) = 52819074474709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_107
      · exact prime_oneHundredElevenDE_41136350837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52819074474709) ^ 26409537237354 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 52819074474709) ^ 17606358158236 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 52819074474709) ^ 493636210044 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 52819074474709) ^ 1284 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_54836194679887 : Nat.Prime 54836194679887 := by
  apply lucas_primality 54836194679887 (3 : ZMod 54836194679887)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (149, 1), (632350777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (149, 1), (632350777, 1)] : List FactorBlock).map factorBlockValue).prod) = 54836194679887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_97
      · exact prime_oneHundredElevenDE_149
      · exact prime_oneHundredElevenDE_632350777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54836194679887) ^ 27418097339943 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 54836194679887) ^ 18278731559962 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 54836194679887) ^ 565321594638 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 54836194679887) ^ 368028152214 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 54836194679887) ^ 86718 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_57539984168959 : Nat.Prime 57539984168959 := by
  apply lucas_primality 57539984168959 (6 : ZMod 57539984168959)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (285101, 1), (33637193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (285101, 1), (33637193, 1)] : List FactorBlock).map factorBlockValue).prod) = 57539984168959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_285101
      · exact prime_oneHundredElevenDE_33637193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 57539984168959) ^ 28769992084479 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 57539984168959) ^ 19179994722986 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 57539984168959) ^ 201823158 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 57539984168959) ^ 1710606 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_64997993247307 : Nat.Prime 64997993247307 := by
  apply lucas_primality 64997993247307 (3 : ZMod 64997993247307)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (151, 1), (727, 1), (14097409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (151, 1), (727, 1), (14097409, 1)] : List FactorBlock).map factorBlockValue).prod) = 64997993247307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_151
      · exact prime_oneHundredElevenDE_727
      · exact prime_oneHundredElevenDE_14097409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64997993247307) ^ 32498996623653 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 21665997749102 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 9285427606758 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 430450286406 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 89405767878 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 4610634 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_94038371110043 : Nat.Prime 94038371110043 := by
  apply lucas_primality 94038371110043 (2 : ZMod 94038371110043)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (41, 1), (62581, 1), (63409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (41, 1), (62581, 1), (63409, 1)] : List FactorBlock).map factorBlockValue).prod) = 94038371110043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_62581
      · exact prime_oneHundredElevenDE_63409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94038371110043) ^ 47019185555021 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94038371110043) ^ 5531668888826 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94038371110043) ^ 2293618807562 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94038371110043) ^ 1502666482 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94038371110043) ^ 1483044538 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_103318108854497 : Nat.Prime 103318108854497 := by
  apply lucas_primality 103318108854497 (3 : ZMod 103318108854497)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (229, 1), (14099086907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (229, 1), (14099086907, 1)] : List FactorBlock).map factorBlockValue).prod) = 103318108854497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_229
      · exact prime_oneHundredElevenDE_14099086907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103318108854497) ^ 51659054427248 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 103318108854497) ^ 451170781024 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 103318108854497) ^ 7328 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_154743408951839 : Nat.Prime 154743408951839 := by
  apply lucas_primality 154743408951839 (7 : ZMod 154743408951839)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (383, 1), (28859270599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (383, 1), (28859270599, 1)] : List FactorBlock).map factorBlockValue).prod) = 154743408951839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_383
      · exact prime_oneHundredElevenDE_28859270599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 154743408951839) ^ 77371704475919 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 154743408951839) ^ 22106201278834 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 154743408951839) ^ 404029788386 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 154743408951839) ^ 5362 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_234980270081387 : Nat.Prime 234980270081387 := by
  apply lucas_primality 234980270081387 (2 : ZMod 234980270081387)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (83, 1), (34525458431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (83, 1), (34525458431, 1)] : List FactorBlock).map factorBlockValue).prod) = 234980270081387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_83
      · exact prime_oneHundredElevenDE_34525458431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 234980270081387) ^ 117490135040693 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 234980270081387) ^ 5731226099546 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 234980270081387) ^ 2831087591342 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 234980270081387) ^ 6806 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_264192662834041 : Nat.Prime 264192662834041 := by
  apply lucas_primality 264192662834041 (11 : ZMod 264192662834041)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (97, 1), (109, 1), (2017, 1), (103237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (97, 1), (109, 1), (2017, 1), (103237, 1)] : List FactorBlock).map factorBlockValue).prod) = 264192662834041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_97
      · exact prime_oneHundredElevenDE_109
      · exact prime_oneHundredElevenDE_2017
      · exact prime_oneHundredElevenDE_103237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 264192662834041) ^ 132096331417020 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 264192662834041) ^ 88064220944680 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 264192662834041) ^ 52838532566808 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 264192662834041) ^ 2723635699320 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 264192662834041) ^ 2423785897560 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 264192662834041) ^ 130982976120 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 264192662834041) ^ 2559088920 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_336751159161191 : Nat.Prime 336751159161191 := by
  apply lucas_primality 336751159161191 (11 : ZMod 336751159161191)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (1772374521901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (1772374521901, 1)] : List FactorBlock).map factorBlockValue).prod) = 336751159161191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_1772374521901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 336751159161191) ^ 168375579580595 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 336751159161191) ^ 67350231832238 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 336751159161191) ^ 17723745219010 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 336751159161191) ^ 190 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_401209794293041 : Nat.Prime 401209794293041 := by
  apply lucas_primality 401209794293041 (11 : ZMod 401209794293041)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (97, 1), (5651, 1), (1016581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (97, 1), (5651, 1), (1016581, 1)] : List FactorBlock).map factorBlockValue).prod) = 401209794293041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_97
      · exact prime_oneHundredElevenDE_5651
      · exact prime_oneHundredElevenDE_1016581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 401209794293041) ^ 200604897146520 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 401209794293041) ^ 133736598097680 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 401209794293041) ^ 80241958858608 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 401209794293041) ^ 4136183446320 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 401209794293041) ^ 70998017040 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 401209794293041) ^ 394665840 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_419570339988143 : Nat.Prime 419570339988143 := by
  apply lucas_primality 419570339988143 (5 : ZMod 419570339988143)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (47, 1), (91092127657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (47, 1), (91092127657, 1)] : List FactorBlock).map factorBlockValue).prod) = 419570339988143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_91092127657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 419570339988143) ^ 209785169994071 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 419570339988143) ^ 59938619998306 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 419570339988143) ^ 8927028510386 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 419570339988143) ^ 4606 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_557403986815121 : Nat.Prime 557403986815121 := by
  apply lucas_primality 557403986815121 (3 : ZMod 557403986815121)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (6967549835189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (6967549835189, 1)] : List FactorBlock).map factorBlockValue).prod) = 557403986815121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_6967549835189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 557403986815121) ^ 278701993407560 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 557403986815121) ^ 111480797363024 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 557403986815121) ^ 80 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_571123394779433 : Nat.Prime 571123394779433 := by
  apply lucas_primality 571123394779433 (3 : ZMod 571123394779433)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (29, 1), (223794433691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (29, 1), (223794433691, 1)] : List FactorBlock).map factorBlockValue).prod) = 571123394779433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_29
      · exact prime_oneHundredElevenDE_223794433691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 571123394779433) ^ 285561697389716 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 571123394779433) ^ 51920308616312 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 571123394779433) ^ 19693910164808 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 571123394779433) ^ 2552 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_677310384682937 : Nat.Prime 677310384682937 := by
  apply lucas_primality 677310384682937 (3 : ZMod 677310384682937)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (13291, 1), (148139759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (13291, 1), (148139759, 1)] : List FactorBlock).map factorBlockValue).prod) = 677310384682937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_43
      · exact prime_oneHundredElevenDE_13291
      · exact prime_oneHundredElevenDE_148139759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 677310384682937) ^ 338655192341468 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 677310384682937) ^ 15751404294952 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 677310384682937) ^ 50960077096 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 677310384682937) ^ 4572104 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_895863249330583 : Nat.Prime 895863249330583 := by
  apply lucas_primality 895863249330583 (6 : ZMod 895863249330583)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (11485426273469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (11485426273469, 1)] : List FactorBlock).map factorBlockValue).prod) = 895863249330583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_11485426273469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 895863249330583) ^ 447931624665291 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 895863249330583) ^ 298621083110194 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 895863249330583) ^ 68912557640814 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 895863249330583) ^ 78 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1077761218736687 : Nat.Prime 1077761218736687 := by
  apply lucas_primality 1077761218736687 (5 : ZMod 1077761218736687)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (1324030981249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (1324030981249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1077761218736687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_37
      · exact prime_oneHundredElevenDE_1324030981249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1077761218736687) ^ 538880609368343 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1077761218736687) ^ 97978292612426 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1077761218736687) ^ 29128681587478 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1077761218736687) ^ 814 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1106396084923873 : Nat.Prime 1106396084923873 := by
  apply lucas_primality 1106396084923873 (11 : ZMod 1106396084923873)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (71, 1), (162323369267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (71, 1), (162323369267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1106396084923873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_71
      · exact prime_oneHundredElevenDE_162323369267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1106396084923873) ^ 553198042461936 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1106396084923873) ^ 368798694974624 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1106396084923873) ^ 15583043449632 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1106396084923873) ^ 6816 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1114807973630243 : Nat.Prime 1114807973630243 := by
  apply lucas_primality 1114807973630243 (2 : ZMod 1114807973630243)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (557403986815121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (557403986815121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1114807973630243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_557403986815121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1114807973630243) ^ 557403986815121 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1114807973630243) ^ 2 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1469966823432763 : Nat.Prime 1469966823432763 := by
  apply lucas_primality 1469966823432763 (2 : ZMod 1469966823432763)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1381, 1), (177403671667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1381, 1), (177403671667, 1)] : List FactorBlock).map factorBlockValue).prod) = 1469966823432763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_1381
      · exact prime_oneHundredElevenDE_177403671667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1469966823432763) ^ 734983411716381 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1469966823432763) ^ 489988941144254 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1469966823432763) ^ 1064422030002 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1469966823432763) ^ 8286 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1721294803250761 : Nat.Prime 1721294803250761 := by
  apply lucas_primality 1721294803250761 (11 : ZMod 1721294803250761)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (14344123360423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (14344123360423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1721294803250761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_14344123360423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1721294803250761) ^ 860647401625380 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1721294803250761) ^ 573764934416920 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1721294803250761) ^ 344258960650152 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1721294803250761) ^ 120 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1748439617896709 : Nat.Prime 1748439617896709 := by
  apply lucas_primality 1748439617896709 (2 : ZMod 1748439617896709)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (31, 1), (41, 1), (557, 1), (2440447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (31, 1), (41, 1), (557, 1), (2440447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1748439617896709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_557
      · exact prime_oneHundredElevenDE_2440447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1748439617896709) ^ 874219808948354 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1748439617896709) ^ 158949056172428 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1748439617896709) ^ 76019113821596 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1748439617896709) ^ 56401277996668 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1748439617896709) ^ 42644868729188 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1748439617896709) ^ 3139029834644 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1748439617896709) ^ 716442364 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2109389251383101 : Nat.Prime 2109389251383101 := by
  apply lucas_primality 2109389251383101 (3 : ZMod 2109389251383101)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (19, 1), (43271, 1), (25657019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (19, 1), (43271, 1), (25657019, 1)] : List FactorBlock).map factorBlockValue).prod) = 2109389251383101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_43271
      · exact prime_oneHundredElevenDE_25657019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2109389251383101) ^ 1054694625691550 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2109389251383101) ^ 421877850276620 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2109389251383101) ^ 111020486914900 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2109389251383101) ^ 48748336100 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2109389251383101) ^ 82214900 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2211422517566347 : Nat.Prime 2211422517566347 := by
  apply lucas_primality 2211422517566347 (2 : ZMod 2211422517566347)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (220889, 1), (238368217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (220889, 1), (238368217, 1)] : List FactorBlock).map factorBlockValue).prod) = 2211422517566347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_220889
      · exact prime_oneHundredElevenDE_238368217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2211422517566347) ^ 1105711258783173 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211422517566347) ^ 737140839188782 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211422517566347) ^ 315917502509478 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211422517566347) ^ 10011465114 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211422517566347) ^ 9277338 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_3198705040998737 : Nat.Prime 3198705040998737 := by
  apply lucas_primality 3198705040998737 (3 : ZMod 3198705040998737)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (83, 1), (443, 1), (126445663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (83, 1), (443, 1), (126445663, 1)] : List FactorBlock).map factorBlockValue).prod) = 3198705040998737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_43
      · exact prime_oneHundredElevenDE_83
      · exact prime_oneHundredElevenDE_443
      · exact prime_oneHundredElevenDE_126445663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3198705040998737) ^ 1599352520499368 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3198705040998737) ^ 74388489325552 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3198705040998737) ^ 38538614951792 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3198705040998737) ^ 7220553139952 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3198705040998737) ^ 25297072 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_6122334382059101 : Nat.Prime 6122334382059101 := by
  apply lucas_primality 6122334382059101 (2 : ZMod 6122334382059101)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (823, 1), (3571, 1), (20831827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (823, 1), (3571, 1), (20831827, 1)] : List FactorBlock).map factorBlockValue).prod) = 6122334382059101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_823
      · exact prime_oneHundredElevenDE_3571
      · exact prime_oneHundredElevenDE_20831827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6122334382059101) ^ 3061167191029550 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6122334382059101) ^ 1224466876411820 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6122334382059101) ^ 7439045421700 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6122334382059101) ^ 1714459362100 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6122334382059101) ^ 293893300 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_6415641575705533 : Nat.Prime 6415641575705533 := by
  apply lucas_primality 6415641575705533 (6 : ZMod 6415641575705533)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8053, 1), (66389767537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8053, 1), (66389767537, 1)] : List FactorBlock).map factorBlockValue).prod) = 6415641575705533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_8053
      · exact prime_oneHundredElevenDE_66389767537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6415641575705533) ^ 3207820787852766 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6415641575705533) ^ 2138547191901844 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6415641575705533) ^ 796677210444 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6415641575705533) ^ 96636 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_9027683626564129 : Nat.Prime 9027683626564129 := by
  apply lucas_primality 9027683626564129 (11 : ZMod 9027683626564129)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (94038371110043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (94038371110043, 1)] : List FactorBlock).map factorBlockValue).prod) = 9027683626564129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_94038371110043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 9027683626564129) ^ 4513841813282064 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 9027683626564129) ^ 3009227875521376 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 9027683626564129) ^ 96 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_10707544262372981 : Nat.Prime 10707544262372981 := by
  apply lucas_primality 10707544262372981 (2 : ZMod 10707544262372981)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (17483, 1), (20533, 1), (135581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (17483, 1), (20533, 1), (135581, 1)] : List FactorBlock).map factorBlockValue).prod) = 10707544262372981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_17483
      · exact prime_oneHundredElevenDE_20533
      · exact prime_oneHundredElevenDE_135581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10707544262372981) ^ 5353772131186490 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10707544262372981) ^ 2141508852474596 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10707544262372981) ^ 973413114761180 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10707544262372981) ^ 612454628060 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10707544262372981) ^ 521479777060 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10707544262372981) ^ 78975256580 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_22965055844998711 : Nat.Prime 22965055844998711 := by
  apply lucas_primality 22965055844998711 (11 : ZMod 22965055844998711)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (26893, 1), (28464725449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (26893, 1), (28464725449, 1)] : List FactorBlock).map factorBlockValue).prod) = 22965055844998711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_26893
      · exact prime_oneHundredElevenDE_28464725449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22965055844998711) ^ 11482527922499355 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22965055844998711) ^ 7655018614999570 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22965055844998711) ^ 4593011168999742 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22965055844998711) ^ 853941763470 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22965055844998711) ^ 806790 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_26169823839032213 : Nat.Prime 26169823839032213 := by
  apply lucas_primality 26169823839032213 (2 : ZMod 26169823839032213)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (89, 1), (4349, 1), (6299, 1), (141233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (89, 1), (4349, 1), (6299, 1), (141233, 1)] : List FactorBlock).map factorBlockValue).prod) = 26169823839032213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_89
      · exact prime_oneHundredElevenDE_4349
      · exact prime_oneHundredElevenDE_6299
      · exact prime_oneHundredElevenDE_141233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26169823839032213) ^ 13084911919516106 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 1377359149422748 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 294042964483508 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 6017434775588 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 4154599752188 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 185295390164 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_36942179378870593 : Nat.Prime 36942179378870593 := by
  apply lucas_primality 36942179378870593 (5 : ZMod 36942179378870593)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (37, 1), (61, 1), (2521, 1), (1252429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (37, 1), (61, 1), (2521, 1), (1252429, 1)] : List FactorBlock).map factorBlockValue).prod) = 36942179378870593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_37
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_2521
      · exact prime_oneHundredElevenDE_1252429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36942179378870593) ^ 18471089689435296 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 36942179378870593) ^ 12314059792956864 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 36942179378870593) ^ 998437280510016 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 36942179378870593) ^ 605609498014272 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 36942179378870593) ^ 14653779999552 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 36942179378870593) ^ 29496426048 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_40111027163996851 : Nat.Prime 40111027163996851 := by
  apply lucas_primality 40111027163996851 (15 : ZMod 40111027163996851)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (101, 1), (263, 1), (1118543537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (101, 1), (263, 1), (1118543537, 1)] : List FactorBlock).map factorBlockValue).prod) = 40111027163996851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_101
      · exact prime_oneHundredElevenDE_263
      · exact prime_oneHundredElevenDE_1118543537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 40111027163996851) ^ 20055513581998425 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (15 : ZMod 40111027163996851) ^ 13370342387998950 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (15 : ZMod 40111027163996851) ^ 8022205432799370 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (15 : ZMod 40111027163996851) ^ 397138882811850 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (15 : ZMod 40111027163996851) ^ 152513411269950 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (15 : ZMod 40111027163996851) ^ 35860050 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_42892433318047567 : Nat.Prime 42892433318047567 := by
  apply lucas_primality 42892433318047567 (5 : ZMod 42892433318047567)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (47, 1), (3119, 1), (3911, 1), (1133537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (47, 1), (3119, 1), (3911, 1), (1133537, 1)] : List FactorBlock).map factorBlockValue).prod) = 42892433318047567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_3119
      · exact prime_oneHundredElevenDE_3911
      · exact prime_oneHundredElevenDE_1133537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 42892433318047567) ^ 21446216659023783 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42892433318047567) ^ 14297477772682522 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42892433318047567) ^ 3899312119822506 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42892433318047567) ^ 912604964213778 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42892433318047567) ^ 13751982468114 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42892433318047567) ^ 10967126903106 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 42892433318047567) ^ 37839464718 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_48735591754852333 : Nat.Prime 48735591754852333 := by
  apply lucas_primality 48735591754852333 (2 : ZMod 48735591754852333)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 2), (19, 1), (131, 1), (419, 1), (10728017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 2), (19, 1), (131, 1), (419, 1), (10728017, 1)] : List FactorBlock).map factorBlockValue).prod) = 48735591754852333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_131
      · exact prime_oneHundredElevenDE_419
      · exact prime_oneHundredElevenDE_10728017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48735591754852333) ^ 24367795877426166 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48735591754852333) ^ 16245197251617444 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48735591754852333) ^ 4430508341350212 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48735591754852333) ^ 2565031144992228 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48735591754852333) ^ 372027417975972 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48735591754852333) ^ 116314061467428 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48735591754852333) ^ 4542833196 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_49362491128819369 : Nat.Prime 49362491128819369 := by
  apply lucas_primality 49362491128819369 (11 : ZMod 49362491128819369)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (433, 1), (5231, 1), (908057209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (433, 1), (5231, 1), (908057209, 1)] : List FactorBlock).map factorBlockValue).prod) = 49362491128819369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_433
      · exact prime_oneHundredElevenDE_5231
      · exact prime_oneHundredElevenDE_908057209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 49362491128819369) ^ 24681245564409684 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49362491128819369) ^ 16454163709606456 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49362491128819369) ^ 114001134246696 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49362491128819369) ^ 9436530515928 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 49362491128819369) ^ 54360552 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_73544037168527441 : Nat.Prime 73544037168527441 := by
  apply lucas_primality 73544037168527441 (6 : ZMod 73544037168527441)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (29, 1), (16273, 1), (1948013029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (29, 1), (16273, 1), (1948013029, 1)] : List FactorBlock).map factorBlockValue).prod) = 73544037168527441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_29
      · exact prime_oneHundredElevenDE_16273
      · exact prime_oneHundredElevenDE_1948013029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 73544037168527441) ^ 36772018584263720 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 73544037168527441) ^ 14708807433705488 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 73544037168527441) ^ 2536001281673360 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 73544037168527441) ^ 4519390227280 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 73544037168527441) ^ 37753360 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_158696615200507393 : Nat.Prime 158696615200507393 := by
  apply lucas_primality 158696615200507393 (5 : ZMod 158696615200507393)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (103318108854497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (103318108854497, 1)] : List FactorBlock).map factorBlockValue).prod) = 158696615200507393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_103318108854497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 158696615200507393) ^ 79348307600253696 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 158696615200507393) ^ 52898871733502464 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 158696615200507393) ^ 1536 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_197449964515277477 : Nat.Prime 197449964515277477 := by
  apply lucas_primality 197449964515277477 (2 : ZMod 197449964515277477)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (49362491128819369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (49362491128819369, 1)] : List FactorBlock).map factorBlockValue).prod) = 197449964515277477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_49362491128819369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 197449964515277477) ^ 98724982257638738 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 197449964515277477) ^ 4 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_291042764346141823 : Nat.Prime 291042764346141823 := by
  apply lucas_primality 291042764346141823 (3 : ZMod 291042764346141823)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (101, 1), (2137, 1), (6871, 1), (667519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (101, 1), (2137, 1), (6871, 1), (667519, 1)] : List FactorBlock).map factorBlockValue).prod) = 291042764346141823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_101
      · exact prime_oneHundredElevenDE_2137
      · exact prime_oneHundredElevenDE_6871
      · exact prime_oneHundredElevenDE_667519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 291042764346141823) ^ 145521382173070911 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 291042764346141823) ^ 97014254782047274 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 291042764346141823) ^ 41577537763734546 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 291042764346141823) ^ 2881611528179622 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 291042764346141823) ^ 136192215417006 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 291042764346141823) ^ 42358137730482 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 291042764346141823) ^ 436006711938 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_303522685959904907 : Nat.Prime 303522685959904907 := by
  apply lucas_primality 303522685959904907 (6 : ZMod 303522685959904907)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1769947, 1), (7794858109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1769947, 1), (7794858109, 1)] : List FactorBlock).map factorBlockValue).prod) = 303522685959904907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_1769947
      · exact prime_oneHundredElevenDE_7794858109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 303522685959904907) ^ 151761342979952453 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 303522685959904907) ^ 27592971450900446 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 303522685959904907) ^ 171486878398 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 303522685959904907) ^ 38938834 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_332471506917410563 : Nat.Prime 332471506917410563 := by
  apply lucas_primality 332471506917410563 (2 : ZMod 332471506917410563)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (12263, 1), (347586660433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (12263, 1), (347586660433, 1)] : List FactorBlock).map factorBlockValue).prod) = 332471506917410563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_12263
      · exact prime_oneHundredElevenDE_347586660433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 332471506917410563) ^ 166235753458705281 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 332471506917410563) ^ 110823835639136854 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 332471506917410563) ^ 25574731301339274 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 332471506917410563) ^ 27111759513774 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 332471506917410563) ^ 956514 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_393090184979942591 : Nat.Prime 393090184979942591 := by
  apply lucas_primality 393090184979942591 (11 : ZMod 393090184979942591)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (521, 1), (10778453111597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (521, 1), (10778453111597, 1)] : List FactorBlock).map factorBlockValue).prod) = 393090184979942591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_521
      · exact prime_oneHundredElevenDE_10778453111597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 393090184979942591) ^ 196545092489971295 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 393090184979942591) ^ 78618036995988518 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 393090184979942591) ^ 56155740711420370 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 393090184979942591) ^ 754491717811790 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 393090184979942591) ^ 36470 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_604005656150070457 : Nat.Prime 604005656150070457 := by
  apply lucas_primality 604005656150070457 (10 : ZMod 604005656150070457)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (9041, 1), (36017, 1), (3360299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (9041, 1), (36017, 1), (3360299, 1)] : List FactorBlock).map factorBlockValue).prod) = 604005656150070457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_9041
      · exact prime_oneHundredElevenDE_36017
      · exact prime_oneHundredElevenDE_3360299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 604005656150070457) ^ 302002828075035228 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 201335218716690152 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 26261115484785672 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 66807394773816 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 16770015718968 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 179747592744 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1113956130079478701 : Nat.Prime 1113956130079478701 := by
  apply lucas_primality 1113956130079478701 (2 : ZMod 1113956130079478701)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (7, 1), (23, 1), (2562585990521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (7, 1), (23, 1), (2562585990521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113956130079478701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_2562585990521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1113956130079478701) ^ 556978065039739350 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113956130079478701) ^ 371318710026492900 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113956130079478701) ^ 222791226015895740 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113956130079478701) ^ 159136590011354100 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113956130079478701) ^ 48432875220846900 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113956130079478701) ^ 434700 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1308672380247113533 : Nat.Prime 1308672380247113533 := by
  apply lucas_primality 1308672380247113533 (2 : ZMod 1308672380247113533)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (33569, 1), (57107, 1), (1160983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (33569, 1), (57107, 1), (1160983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1308672380247113533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_33569
      · exact prime_oneHundredElevenDE_57107
      · exact prime_oneHundredElevenDE_1160983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1308672380247113533) ^ 654336190123556766 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308672380247113533) ^ 436224126749037844 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308672380247113533) ^ 186953197178159076 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308672380247113533) ^ 38984550634428 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308672380247113533) ^ 22916146536276 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308672380247113533) ^ 1127210631204 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2600804284726294481 : Nat.Prime 2600804284726294481 := by
  apply lucas_primality 2600804284726294481 (3 : ZMod 2600804284726294481)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (431, 1), (18521, 1), (4072639631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (431, 1), (18521, 1), (4072639631, 1)] : List FactorBlock).map factorBlockValue).prod) = 2600804284726294481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_431
      · exact prime_oneHundredElevenDE_18521
      · exact prime_oneHundredElevenDE_4072639631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2600804284726294481) ^ 1300402142363147240 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2600804284726294481) ^ 520160856945258896 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2600804284726294481) ^ 6034348688460080 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2600804284726294481) ^ 140424614476880 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2600804284726294481) ^ 638604080 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2795093337911418961 : Nat.Prime 2795093337911418961 := by
  apply lucas_primality 2795093337911418961 (31 : ZMod 2795093337911418961)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (895863249330583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (895863249330583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2795093337911418961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_895863249330583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 2795093337911418961) ^ 1397546668955709480 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (31 : ZMod 2795093337911418961) ^ 931697779303806320 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (31 : ZMod 2795093337911418961) ^ 559018667582283792 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (31 : ZMod 2795093337911418961) ^ 215007179839339920 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (31 : ZMod 2795093337911418961) ^ 3120 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_3787847943891692353 : Nat.Prime 3787847943891692353 := by
  apply lucas_primality 3787847943891692353 (10 : ZMod 3787847943891692353)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (691, 1), (4078638558563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (691, 1), (4078638558563, 1)] : List FactorBlock).map factorBlockValue).prod) = 3787847943891692353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_691
      · exact prime_oneHundredElevenDE_4078638558563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3787847943891692353) ^ 1893923971945846176 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 3787847943891692353) ^ 1262615981297230784 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 3787847943891692353) ^ 541121134841670336 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 3787847943891692353) ^ 5481690222708672 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (10 : ZMod 3787847943891692353) ^ 928704 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_9347691976911383813 : Nat.Prime 9347691976911383813 := by
  apply lucas_primality 9347691976911383813 (2 : ZMod 9347691976911383813)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (211, 1), (6894161, 1), (12263353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (211, 1), (6894161, 1), (12263353, 1)] : List FactorBlock).map factorBlockValue).prod) = 9347691976911383813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_131
      · exact prime_oneHundredElevenDE_211
      · exact prime_oneHundredElevenDE_6894161
      · exact prime_oneHundredElevenDE_12263353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9347691976911383813) ^ 4673845988455691906 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9347691976911383813) ^ 71356427304667052 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9347691976911383813) ^ 44301857710480492 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9347691976911383813) ^ 1355885361092 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9347691976911383813) ^ 762246016804 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_21131190407207992303 : Nat.Prime 21131190407207992303 := by
  apply lucas_primality 21131190407207992303 (3 : ZMod 21131190407207992303)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5273, 1), (5381, 1), (160579, 1), (257657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5273, 1), (5381, 1), (160579, 1), (257657, 1)] : List FactorBlock).map factorBlockValue).prod) = 21131190407207992303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5273
      · exact prime_oneHundredElevenDE_5381
      · exact prime_oneHundredElevenDE_160579
      · exact prime_oneHundredElevenDE_257657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21131190407207992303) ^ 10565595203603996151 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 21131190407207992303) ^ 7043730135735997434 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 21131190407207992303) ^ 4007432279007774 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 21131190407207992303) ^ 3927000633192342 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 21131190407207992303) ^ 131593735215738 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 21131190407207992303) ^ 82012871403486 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_31196601207145065257 : Nat.Prime 31196601207145065257 := by
  apply lucas_primality 31196601207145065257 (3 : ZMod 31196601207145065257)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (146921, 1), (26541986175517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (146921, 1), (26541986175517, 1)] : List FactorBlock).map factorBlockValue).prod) = 31196601207145065257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_146921
      · exact prime_oneHundredElevenDE_26541986175517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31196601207145065257) ^ 15598300603572532628 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31196601207145065257) ^ 212335889404136 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 31196601207145065257) ^ 1175368 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_46590393394217823809 : Nat.Prime 46590393394217823809 := by
  apply lucas_primality 46590393394217823809 (3 : ZMod 46590393394217823809)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 2), (103, 1), (3493681386313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 2), (103, 1), (3493681386313, 1)] : List FactorBlock).map factorBlockValue).prod) = 46590393394217823809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_103
      · exact prime_oneHundredElevenDE_3493681386313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46590393394217823809) ^ 23295196697108911904 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 46590393394217823809) ^ 6655770484888260544 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 46590393394217823809) ^ 2740611376130460224 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 46590393394217823809) ^ 452333916448716736 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 46590393394217823809) ^ 13335616 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_47010106916580133433 : Nat.Prime 47010106916580133433 := by
  apply lucas_primality 47010106916580133433 (3 : ZMod 47010106916580133433)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (42892433318047567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (42892433318047567, 1)] : List FactorBlock).map factorBlockValue).prod) = 47010106916580133433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_137
      · exact prime_oneHundredElevenDE_42892433318047567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47010106916580133433) ^ 23505053458290066716 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 47010106916580133433) ^ 343139466544380536 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 47010106916580133433) ^ 1096 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_50825810824775294729 : Nat.Prime 50825810824775294729 := by
  apply lucas_primality 50825810824775294729 (3 : ZMod 50825810824775294729)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (269146453, 1), (3372155771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (269146453, 1), (3372155771, 1)] : List FactorBlock).map factorBlockValue).prod) = 50825810824775294729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_269146453
      · exact prime_oneHundredElevenDE_3372155771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50825810824775294729) ^ 25412905412387647364 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 50825810824775294729) ^ 7260830117825042104 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 50825810824775294729) ^ 188840723176 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 50825810824775294729) ^ 15072201368 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_59698005142953515147 : Nat.Prime 59698005142953515147 := by
  apply lucas_primality 59698005142953515147 (2 : ZMod 59698005142953515147)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (151, 1), (5521, 1), (453218926397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (151, 1), (5521, 1), (453218926397, 1)] : List FactorBlock).map factorBlockValue).prod) = 59698005142953515147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_79
      · exact prime_oneHundredElevenDE_151
      · exact prime_oneHundredElevenDE_5521
      · exact prime_oneHundredElevenDE_453218926397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59698005142953515147) ^ 29849002571476757573 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 59698005142953515147) ^ 755670951176626774 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 59698005142953515147) ^ 395351027436778246 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 59698005142953515147) ^ 10812897145979626 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 59698005142953515147) ^ 131720018 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_113723208278657738867 : Nat.Prime 113723208278657738867 := by
  apply lucas_primality 113723208278657738867 (2 : ZMod 113723208278657738867)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7537, 1), (1077761218736687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7537, 1), (1077761218736687, 1)] : List FactorBlock).map factorBlockValue).prod) = 113723208278657738867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_7537
      · exact prime_oneHundredElevenDE_1077761218736687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113723208278657738867) ^ 56861604139328869433 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113723208278657738867) ^ 16246172611236819838 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113723208278657738867) ^ 15088657062313618 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113723208278657738867) ^ 105518 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_154536888817040220149 : Nat.Prime 154536888817040220149 := by
  apply lucas_primality 154536888817040220149 (2 : ZMod 154536888817040220149)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (84913, 1), (64997993247307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (84913, 1), (64997993247307, 1)] : List FactorBlock).map factorBlockValue).prod) = 154536888817040220149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_84913
      · exact prime_oneHundredElevenDE_64997993247307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 154536888817040220149) ^ 77268444408520110074 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 154536888817040220149) ^ 22076698402434317164 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 154536888817040220149) ^ 1819943810924596 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 154536888817040220149) ^ 2377564 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_187179607242870391543 : Nat.Prime 187179607242870391543 := by
  apply lucas_primality 187179607242870391543 (3 : ZMod 187179607242870391543)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31196601207145065257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31196601207145065257, 1)] : List FactorBlock).map factorBlockValue).prod) = 187179607242870391543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_31196601207145065257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 187179607242870391543) ^ 93589803621435195771 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187179607242870391543) ^ 62393202414290130514 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 187179607242870391543) ^ 6 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_233708306012414121437 : Nat.Prime 233708306012414121437 := by
  apply lucas_primality 233708306012414121437 (2 : ZMod 233708306012414121437)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (587, 1), (757, 1), (1901191, 1), (69159911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (587, 1), (757, 1), (1901191, 1), (69159911, 1)] : List FactorBlock).map factorBlockValue).prod) = 233708306012414121437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_587
      · exact prime_oneHundredElevenDE_757
      · exact prime_oneHundredElevenDE_1901191
      · exact prime_oneHundredElevenDE_69159911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 233708306012414121437) ^ 116854153006207060718 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233708306012414121437) ^ 398140214671915028 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233708306012414121437) ^ 308729598431194348 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233708306012414121437) ^ 122927315568196 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 233708306012414121437) ^ 3379245326276 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_241730164246224144299 : Nat.Prime 241730164246224144299 := by
  apply lucas_primality 241730164246224144299 (2 : ZMod 241730164246224144299)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (82223, 1), (1469966823432763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (82223, 1), (1469966823432763, 1)] : List FactorBlock).map factorBlockValue).prod) = 241730164246224144299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_82223
      · exact prime_oneHundredElevenDE_1469966823432763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 241730164246224144299) ^ 120865082123112072149 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 241730164246224144299) ^ 2939933646865526 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 241730164246224144299) ^ 164446 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_6863
      · exact prime_oneHundredElevenDE_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_265282037042082037063 : Nat.Prime 265282037042082037063 := by
  apply lucas_primality 265282037042082037063 (5 : ZMod 265282037042082037063)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (2600804284726294481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (2600804284726294481, 1)] : List FactorBlock).map factorBlockValue).prod) = 265282037042082037063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_2600804284726294481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 265282037042082037063) ^ 132641018521041018531 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 265282037042082037063) ^ 88427345680694012354 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 265282037042082037063) ^ 15604825708357766886 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 265282037042082037063) ^ 102 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_346883992808737608223 : Nat.Prime 346883992808737608223 := by
  apply lucas_primality 346883992808737608223 (3 : ZMod 346883992808737608223)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (25639, 1), (2824631, 1), (798307493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (25639, 1), (2824631, 1), (798307493, 1)] : List FactorBlock).map factorBlockValue).prod) = 346883992808737608223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_25639
      · exact prime_oneHundredElevenDE_2824631
      · exact prime_oneHundredElevenDE_798307493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 346883992808737608223) ^ 173441996404368804111 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 346883992808737608223) ^ 115627997602912536074 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 346883992808737608223) ^ 13529544553560498 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 346883992808737608223) ^ 122806834878162 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 346883992808737608223) ^ 434524285254 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_354881636081862111977 : Nat.Prime 354881636081862111977 := by
  apply lucas_primality 354881636081862111977 (3 : ZMod 354881636081862111977)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 2), (4271, 1), (42307, 1), (1452663529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 2), (4271, 1), (42307, 1), (1452663529, 1)] : List FactorBlock).map factorBlockValue).prod) = 354881636081862111977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_4271
      · exact prime_oneHundredElevenDE_42307
      · exact prime_oneHundredElevenDE_1452663529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 354881636081862111977) ^ 177440818040931055988 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 354881636081862111977) ^ 27298587390912470152 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 354881636081862111977) ^ 83090994165736856 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 354881636081862111977) ^ 8388248660549368 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 354881636081862111977) ^ 244297202344 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_404353262509829014897 : Nat.Prime 404353262509829014897 := by
  apply lucas_primality 404353262509829014897 (5 : ZMod 404353262509829014897)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (16267, 1), (57539984168959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (16267, 1), (57539984168959, 1)] : List FactorBlock).map factorBlockValue).prod) = 404353262509829014897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_16267
      · exact prime_oneHundredElevenDE_57539984168959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 404353262509829014897) ^ 202176631254914507448 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 404353262509829014897) ^ 134784420836609671632 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 404353262509829014897) ^ 24857273160990288 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 404353262509829014897) ^ 7027344 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_406978372170460868209 : Nat.Prime 406978372170460868209 := by
  apply lucas_primality 406978372170460868209 (7 : ZMod 406978372170460868209)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (131, 1), (223, 1), (10008199097573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (131, 1), (223, 1), (10008199097573, 1)] : List FactorBlock).map factorBlockValue).prod) = 406978372170460868209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_29
      · exact prime_oneHundredElevenDE_131
      · exact prime_oneHundredElevenDE_223
      · exact prime_oneHundredElevenDE_10008199097573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 406978372170460868209) ^ 203489186085230434104 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 406978372170460868209) ^ 135659457390153622736 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 406978372170460868209) ^ 14033736971395202352 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 406978372170460868209) ^ 3106705131072220368 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 406978372170460868209) ^ 1825015121840631696 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 406978372170460868209) ^ 40664496 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_444566091453594151609 : Nat.Prime 444566091453594151609 := by
  apply lucas_primality 444566091453594151609 (11 : ZMod 444566091453594151609)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (17, 1), (45557, 1), (571369, 1), (1993357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (17, 1), (45557, 1), (571369, 1), (1993357, 1)] : List FactorBlock).map factorBlockValue).prod) = 444566091453594151609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_45557
      · exact prime_oneHundredElevenDE_571369
      · exact prime_oneHundredElevenDE_1993357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 444566091453594151609) ^ 222283045726797075804 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 444566091453594151609) ^ 148188697151198050536 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 444566091453594151609) ^ 63509441636227735944 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 444566091453594151609) ^ 26150946556093773624 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 444566091453594151609) ^ 9758458446640344 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 444566091453594151609) ^ 778071774026232 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 444566091453594151609) ^ 223023819342744 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_665674142227564280339 : Nat.Prime 665674142227564280339 := by
  apply lucas_primality 665674142227564280339 (2 : ZMod 665674142227564280339)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (17093, 1), (3664447, 1), (11234243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (17093, 1), (3664447, 1), (11234243, 1)] : List FactorBlock).map factorBlockValue).prod) = 665674142227564280339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_43
      · exact prime_oneHundredElevenDE_17093
      · exact prime_oneHundredElevenDE_3664447
      · exact prime_oneHundredElevenDE_11234243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 665674142227564280339) ^ 332837071113782140169 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 665674142227564280339) ^ 60515831111596752758 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 665674142227564280339) ^ 15480794005292192566 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 665674142227564280339) ^ 38944254503455466 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 665674142227564280339) ^ 181657462156654 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 665674142227564280339) ^ 59254027372166 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_726114122709561931823 : Nat.Prime 726114122709561931823 := by
  apply lucas_primality 726114122709561931823 (5 : ZMod 726114122709561931823)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2269, 1), (6961, 1), (22986283483379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2269, 1), (6961, 1), (22986283483379, 1)] : List FactorBlock).map factorBlockValue).prod) = 726114122709561931823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_2269
      · exact prime_oneHundredElevenDE_6961
      · exact prime_oneHundredElevenDE_22986283483379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 726114122709561931823) ^ 363057061354780965911 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 726114122709561931823) ^ 320015038655602438 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 726114122709561931823) ^ 104311754447573902 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 726114122709561931823) ^ 31589018 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_23
      · exact prime_oneHundredElevenDE_1549
      · exact prime_oneHundredElevenDE_47713
      · exact prime_oneHundredElevenDE_341461
      · exact prime_oneHundredElevenDE_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1533591234798575041703 : Nat.Prime 1533591234798575041703 := by
  apply lucas_primality 1533591234798575041703 (5 : ZMod 1533591234798575041703)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (903607, 1), (16593677, 1), (51139609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (903607, 1), (16593677, 1), (51139609, 1)] : List FactorBlock).map factorBlockValue).prod) = 1533591234798575041703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_903607
      · exact prime_oneHundredElevenDE_16593677
      · exact prime_oneHundredElevenDE_51139609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1533591234798575041703) ^ 766795617399287520851 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1533591234798575041703) ^ 1697188307304586 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1533591234798575041703) ^ 92420217339326 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1533591234798575041703) ^ 29988325385878 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_2088244364617200082201 : Nat.Prime 2088244364617200082201 := by
  apply lucas_primality 2088244364617200082201 (19 : ZMod 2088244364617200082201)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (131, 1), (503, 1), (52819074474709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (131, 1), (503, 1), (52819074474709, 1)] : List FactorBlock).map factorBlockValue).prod) = 2088244364617200082201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_131
      · exact prime_oneHundredElevenDE_503
      · exact prime_oneHundredElevenDE_52819074474709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 2088244364617200082201) ^ 1044122182308600041100 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (19 : ZMod 2088244364617200082201) ^ 696081454872400027400 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (19 : ZMod 2088244364617200082201) ^ 417648872923440016440 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (19 : ZMod 2088244364617200082201) ^ 15940796676467176200 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (19 : ZMod 2088244364617200082201) ^ 4151579253712127400 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (19 : ZMod 2088244364617200082201) ^ 39535800 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_4160904630773454481613 : Nat.Prime 4160904630773454481613 := by
  apply lucas_primality 4160904630773454481613 (2 : ZMod 4160904630773454481613)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (47, 1), (797, 1), (677310384682937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (47, 1), (797, 1), (677310384682937, 1)] : List FactorBlock).map factorBlockValue).prod) = 4160904630773454481613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_797
      · exact prime_oneHundredElevenDE_677310384682937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4160904630773454481613) ^ 2080452315386727240806 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160904630773454481613) ^ 101485478799352548332 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160904630773454481613) ^ 88529885761137329396 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160904630773454481613) ^ 5220708445136078396 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160904630773454481613) ^ 6143276 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_5394537264573611952703 : Nat.Prime 5394537264573611952703 := by
  apply lucas_primality 5394537264573611952703 (6 : ZMod 5394537264573611952703)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (307, 1), (2647, 1), (1106396084923873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (307, 1), (2647, 1), (1106396084923873, 1)] : List FactorBlock).map factorBlockValue).prod) = 5394537264573611952703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_307
      · exact prime_oneHundredElevenDE_2647
      · exact prime_oneHundredElevenDE_1106396084923873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5394537264573611952703) ^ 2697268632286805976351 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5394537264573611952703) ^ 1798179088191203984234 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5394537264573611952703) ^ 17571782620760950986 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5394537264573611952703) ^ 2037981588429774066 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5394537264573611952703) ^ 4875774 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_8329339924667678775283 : Nat.Prime 8329339924667678775283 := by
  apply lucas_primality 8329339924667678775283 (2 : ZMod 8329339924667678775283)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (4614341, 1), (4121229406079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (4614341, 1), (4121229406079, 1)] : List FactorBlock).map factorBlockValue).prod) = 8329339924667678775283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_73
      · exact prime_oneHundredElevenDE_4614341
      · exact prime_oneHundredElevenDE_4121229406079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8329339924667678775283) ^ 4164669962333839387641 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8329339924667678775283) ^ 2776446641555892925094 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8329339924667678775283) ^ 114100546913255873634 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8329339924667678775283) ^ 1805098479862602 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 8329339924667678775283) ^ 2021081358 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_13650087173644506269753 : Nat.Prime 13650087173644506269753 := by
  apply lucas_primality 13650087173644506269753 (3 : ZMod 13650087173644506269753)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2613833, 1), (21963433, 1), (29721271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2613833, 1), (21963433, 1), (29721271, 1)] : List FactorBlock).map factorBlockValue).prod) = 13650087173644506269753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_2613833
      · exact prime_oneHundredElevenDE_21963433
      · exact prime_oneHundredElevenDE_29721271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13650087173644506269753) ^ 6825043586822253134876 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13650087173644506269753) ^ 5222249154266744 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13650087173644506269753) ^ 621491511533944 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13650087173644506269753) ^ 459269967749512 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_22137827421789521589599 : Nat.Prime 22137827421789521589599 := by
  apply lucas_primality 22137827421789521589599 (11 : ZMod 22137827421789521589599)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (53, 1), (557767883, 1), (1791551689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (53, 1), (557767883, 1), (1791551689, 1)] : List FactorBlock).map factorBlockValue).prod) = 22137827421789521589599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_53
      · exact prime_oneHundredElevenDE_557767883
      · exact prime_oneHundredElevenDE_1791551689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22137827421789521589599) ^ 11068913710894760794799 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22137827421789521589599) ^ 2012529765617229235418 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22137827421789521589599) ^ 1165148811673132715242 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22137827421789521589599) ^ 417694857014896633766 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22137827421789521589599) ^ 39690036118106 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 22137827421789521589599) ^ 12356789679982 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_24746825576811568437479 : Nat.Prime 24746825576811568437479 := by
  apply lucas_primality 24746825576811568437479 (19 : ZMod 24746825576811568437479)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (277287511, 1), (299483516401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (277287511, 1), (299483516401, 1)] : List FactorBlock).map factorBlockValue).prod) = 24746825576811568437479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_149
      · exact prime_oneHundredElevenDE_277287511
      · exact prime_oneHundredElevenDE_299483516401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 24746825576811568437479) ^ 12373412788405784218739 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (19 : ZMod 24746825576811568437479) ^ 166086077696721935822 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (19 : ZMod 24746825576811568437479) ^ 89246087887498 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (19 : ZMod 24746825576811568437479) ^ 82631678278 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_76579866411664230037727 : Nat.Prime 76579866411664230037727 := by
  apply lucas_primality 76579866411664230037727 (5 : ZMod 76579866411664230037727)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (199, 1), (269, 1), (971, 1), (1013, 1), (19653905023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (199, 1), (269, 1), (971, 1), (1013, 1), (19653905023, 1)] : List FactorBlock).map factorBlockValue).prod) = 76579866411664230037727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_37
      · exact prime_oneHundredElevenDE_199
      · exact prime_oneHundredElevenDE_269
      · exact prime_oneHundredElevenDE_971
      · exact prime_oneHundredElevenDE_1013
      · exact prime_oneHundredElevenDE_19653905023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76579866411664230037727) ^ 38289933205832115018863 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 2069726119234168379398 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 384823449304845377074 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 284683518258974832854 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 78867009692754098906 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 75597104058898548902 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 3896419888162 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_85066198311669987329851 : Nat.Prime 85066198311669987329851 := by
  apply lucas_primality 85066198311669987329851 (2 : ZMod 85066198311669987329851)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (2389640179, 1), (237319406381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (2389640179, 1), (237319406381, 1)] : List FactorBlock).map factorBlockValue).prod) = 85066198311669987329851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_2389640179
      · exact prime_oneHundredElevenDE_237319406381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85066198311669987329851) ^ 42533099155834993664925 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 85066198311669987329851) ^ 28355399437223329109950 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 85066198311669987329851) ^ 17013239662333997465970 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 85066198311669987329851) ^ 35597910957150 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 85066198311669987329851) ^ 358446026850 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_88056004170522632356649 : Nat.Prime 88056004170522632356649 := by
  apply lucas_primality 88056004170522632356649 (3 : ZMod 88056004170522632356649)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (241, 1), (1113956130079478701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (241, 1), (1113956130079478701, 1)] : List FactorBlock).map factorBlockValue).prod) = 88056004170522632356649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_41
      · exact prime_oneHundredElevenDE_241
      · exact prime_oneHundredElevenDE_1113956130079478701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 88056004170522632356649) ^ 44028002085261316178324 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 88056004170522632356649) ^ 2147707418793234935528 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 88056004170522632356649) ^ 365377610666069013928 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 88056004170522632356649) ^ 79048 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_90523671985545425071609 : Nat.Prime 90523671985545425071609 := by
  apply lucas_primality 90523671985545425071609 (11 : ZMod 90523671985545425071609)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (428401, 1), (4854599, 1), (95453857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (428401, 1), (4854599, 1), (95453857, 1)] : List FactorBlock).map factorBlockValue).prod) = 90523671985545425071609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_428401
      · exact prime_oneHundredElevenDE_4854599
      · exact prime_oneHundredElevenDE_95453857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 90523671985545425071609) ^ 45261835992772712535804 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 90523671985545425071609) ^ 30174557328515141690536 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 90523671985545425071609) ^ 4764403788712917109032 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 90523671985545425071609) ^ 211305930624684408 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 90523671985545425071609) ^ 18646992673451592 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 90523671985545425071609) ^ 948350070186744 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_94433456025563776121261 : Nat.Prime 94433456025563776121261 := by
  apply lucas_primality 94433456025563776121261 (2 : ZMod 94433456025563776121261)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (31, 1), (831529, 1), (14090079456749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (31, 1), (831529, 1), (14090079456749, 1)] : List FactorBlock).map factorBlockValue).prod) = 94433456025563776121261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_831529
      · exact prime_oneHundredElevenDE_14090079456749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94433456025563776121261) ^ 47216728012781888060630 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94433456025563776121261) ^ 18886691205112755224252 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94433456025563776121261) ^ 7264112001966444317020 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94433456025563776121261) ^ 3046240516953670197460 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94433456025563776121261) ^ 113566040421396940 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94433456025563776121261) ^ 6702123740 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_108267805956440373379271 : Nat.Prime 108267805956440373379271 := by
  apply lucas_primality 108267805956440373379271 (7 : ZMod 108267805956440373379271)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (811, 1), (3323561, 1), (4016750233037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (811, 1), (3323561, 1), (4016750233037, 1)] : List FactorBlock).map factorBlockValue).prod) = 108267805956440373379271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_811
      · exact prime_oneHundredElevenDE_3323561
      · exact prime_oneHundredElevenDE_4016750233037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 108267805956440373379271) ^ 54133902978220186689635 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 108267805956440373379271) ^ 21653561191288074675854 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 108267805956440373379271) ^ 133499144212626847570 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 108267805956440373379271) ^ 32575844389930070 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (7 : ZMod 108267805956440373379271) ^ 26954079710 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_186056529599413169193743 : Nat.Prime 186056529599413169193743 := by
  apply lucas_primality 186056529599413169193743 (5 : ZMod 186056529599413169193743)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (187179607242870391543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (187179607242870391543, 1)] : List FactorBlock).map factorBlockValue).prod) = 186056529599413169193743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_71
      · exact prime_oneHundredElevenDE_187179607242870391543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 186056529599413169193743) ^ 93028264799706584596871 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 186056529599413169193743) ^ 26579504228487595599106 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 186056529599413169193743) ^ 2620514501400185481602 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 186056529599413169193743) ^ 994 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_253186006616388858359513 : Nat.Prime 253186006616388858359513 := by
  apply lucas_primality 253186006616388858359513 (3 : ZMod 253186006616388858359513)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (223, 1), (2011, 1), (6415641575705533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (223, 1), (2011, 1), (6415641575705533, 1)] : List FactorBlock).map factorBlockValue).prod) = 253186006616388858359513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_223
      · exact prime_oneHundredElevenDE_2011
      · exact prime_oneHundredElevenDE_6415641575705533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 253186006616388858359513) ^ 126593003308194429179756 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 253186006616388858359513) ^ 23016909692398987123592 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 253186006616388858359513) ^ 1135363258369456763944 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 253186006616388858359513) ^ 125900550281645379592 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 253186006616388858359513) ^ 39463864 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_325766120880283212823357 : Nat.Prime 325766120880283212823357 := by
  apply lucas_primality 325766120880283212823357 (6 : ZMod 325766120880283212823357)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (2088244364617200082201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (2088244364617200082201, 1)] : List FactorBlock).map factorBlockValue).prod) = 325766120880283212823357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_2088244364617200082201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 325766120880283212823357) ^ 162883060440141606411678 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 325766120880283212823357) ^ 108588706960094404274452 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 325766120880283212823357) ^ 25058932375406400986412 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (6 : ZMod 325766120880283212823357) ^ 156 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_477965436476922562230749 : Nat.Prime 477965436476922562230749 := by
  apply lucas_primality 477965436476922562230749 (2 : ZMod 477965436476922562230749)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (61, 1), (179, 1), (839, 1), (19274603, 1), (96673667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (61, 1), (179, 1), (839, 1), (19274603, 1), (96673667, 1)] : List FactorBlock).map factorBlockValue).prod) = 477965436476922562230749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_61
      · exact prime_oneHundredElevenDE_179
      · exact prime_oneHundredElevenDE_839
      · exact prime_oneHundredElevenDE_19274603
      · exact prime_oneHundredElevenDE_96673667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 477965436476922562230749) ^ 238982718238461281115374 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 477965436476922562230749) ^ 68280776639560366032964 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 477965436476922562230749) ^ 7835498958638074790668 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 477965436476922562230749) ^ 2670197969144818783412 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 477965436476922562230749) ^ 569684668029705080132 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 477965436476922562230749) ^ 24797679956205716 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 477965436476922562230749) ^ 4944111993568244 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_503779834220416936488983 : Nat.Prime 503779834220416936488983 := by
  apply lucas_primality 503779834220416936488983 (5 : ZMod 503779834220416936488983)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41326142149, 1), (468859333643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41326142149, 1), (468859333643, 1)] : List FactorBlock).map factorBlockValue).prod) = 503779834220416936488983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_41326142149
      · exact prime_oneHundredElevenDE_468859333643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 503779834220416936488983) ^ 251889917110208468244491 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 503779834220416936488983) ^ 38752294940032072037614 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 503779834220416936488983) ^ 12190342674718 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 503779834220416936488983) ^ 1074479695874 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_520155629111443002595241 : Nat.Prime 520155629111443002595241 := by
  apply lucas_primality 520155629111443002595241 (3 : ZMod 520155629111443002595241)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (83, 1), (179, 1), (3313, 1), (264192662834041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (83, 1), (179, 1), (3313, 1), (264192662834041, 1)] : List FactorBlock).map factorBlockValue).prod) = 520155629111443002595241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_83
      · exact prime_oneHundredElevenDE_179
      · exact prime_oneHundredElevenDE_3313
      · exact prime_oneHundredElevenDE_264192662834041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 520155629111443002595241) ^ 260077814555721501297620 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 520155629111443002595241) ^ 104031125822288600519048 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 520155629111443002595241) ^ 6266935290499313284280 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 520155629111443002595241) ^ 2905897369337670405560 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 520155629111443002595241) ^ 157004415669013885480 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 520155629111443002595241) ^ 1968849640 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_893418914780840302094543 : Nat.Prime 893418914780840302094543 := by
  apply lucas_primality 893418914780840302094543 (5 : ZMod 893418914780840302094543)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16193, 1), (75937, 1), (5273381, 1), (68889851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16193, 1), (75937, 1), (5273381, 1), (68889851, 1)] : List FactorBlock).map factorBlockValue).prod) = 893418914780840302094543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_16193
      · exact prime_oneHundredElevenDE_75937
      · exact prime_oneHundredElevenDE_5273381
      · exact prime_oneHundredElevenDE_68889851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 893418914780840302094543) ^ 446709457390420151047271 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 893418914780840302094543) ^ 55173155979796226894 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 893418914780840302094543) ^ 11765264821902897166 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 893418914780840302094543) ^ 169420513097923382 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 893418914780840302094543) ^ 12968803122840842 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_35182741055070586984922557 : Nat.Prime 35182741055070586984922557 := by
  apply lucas_primality 35182741055070586984922557 (5 : ZMod 35182741055070586984922557)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (325766120880283212823357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (325766120880283212823357, 1)] : List FactorBlock).map factorBlockValue).prod) = 35182741055070586984922557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_325766120880283212823357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 35182741055070586984922557) ^ 17591370527535293492461278 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35182741055070586984922557) ^ 11727580351690195661640852 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35182741055070586984922557) ^ 108 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_48176073471150253103436541 : Nat.Prime 48176073471150253103436541 := by
  apply lucas_primality 48176073471150253103436541 (2 : ZMod 48176073471150253103436541)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (71, 1), (73, 1), (331, 1), (839, 1), (208141, 1), (893367389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (71, 1), (73, 1), (331, 1), (839, 1), (208141, 1), (893367389, 1)] : List FactorBlock).map factorBlockValue).prod) = 48176073471150253103436541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_71
      · exact prime_oneHundredElevenDE_73
      · exact prime_oneHundredElevenDE_331
      · exact prime_oneHundredElevenDE_839
      · exact prime_oneHundredElevenDE_208141
      · exact prime_oneHundredElevenDE_893367389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48176073471150253103436541) ^ 24088036735575126551718270 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48176073471150253103436541) ^ 16058691157050084367812180 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48176073471150253103436541) ^ 9635214694230050620687308 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48176073471150253103436541) ^ 678536246072538776104740 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48176073471150253103436541) ^ 659946211933565111005980 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48176073471150253103436541) ^ 145547049761783242004340 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48176073471150253103436541) ^ 57420826544875152685860 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48176073471150253103436541) ^ 231458835458416424940 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 48176073471150253103436541) ^ 53926384670338860 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_75118273689418024873360697 : Nat.Prime 75118273689418024873360697 := by
  apply lucas_primality 75118273689418024873360697 (3 : ZMod 75118273689418024873360697)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (31, 1), (337, 1), (587, 1), (10707544262372981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (31, 1), (337, 1), (587, 1), (10707544262372981, 1)] : List FactorBlock).map factorBlockValue).prod) = 75118273689418024873360697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_11
      · exact prime_oneHundredElevenDE_13
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_337
      · exact prime_oneHundredElevenDE_587
      · exact prime_oneHundredElevenDE_10707544262372981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75118273689418024873360697) ^ 37559136844709012436680348 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75118273689418024873360697) ^ 6828933971765274988487336 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75118273689418024873360697) ^ 5778328745339848067181592 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75118273689418024873360697) ^ 2423170119013484673334216 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75118273689418024873360697) ^ 222902889286106898734008 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75118273689418024873360697) ^ 127969801855908049188008 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 75118273689418024873360697) ^ 7015453016 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_81007175392230425588741443 : Nat.Prime 81007175392230425588741443 := by
  apply lucas_primality 81007175392230425588741443 (3 : ZMod 81007175392230425588741443)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 4), (283, 1), (419, 1), (9199, 1), (5155122637909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 4), (283, 1), (419, 1), (9199, 1), (5155122637909, 1)] : List FactorBlock).map factorBlockValue).prod) = 81007175392230425588741443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_7
      · exact prime_oneHundredElevenDE_283
      · exact prime_oneHundredElevenDE_419
      · exact prime_oneHundredElevenDE_9199
      · exact prime_oneHundredElevenDE_5155122637909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81007175392230425588741443) ^ 40503587696115212794370721 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 27002391797410141862913814 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 11572453627461489369820206 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 286244436014948500313574 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 193334547475490275868118 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 8806084943171043112158 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 15713918190138 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_102364761416079008934291059 : Nat.Prime 102364761416079008934291059 := by
  apply lucas_primality 102364761416079008934291059 (2 : ZMod 102364761416079008934291059)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (9923, 1), (37049, 1), (401209794293041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (9923, 1), (37049, 1), (401209794293041, 1)] : List FactorBlock).map factorBlockValue).prod) = 102364761416079008934291059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_347
      · exact prime_oneHundredElevenDE_9923
      · exact prime_oneHundredElevenDE_37049
      · exact prime_oneHundredElevenDE_401209794293041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102364761416079008934291059) ^ 51182380708039504467145529 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 102364761416079008934291059) ^ 294999312438268037274614 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 102364761416079008934291059) ^ 10315908638121435950246 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 102364761416079008934291059) ^ 2762956123406273015042 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 102364761416079008934291059) ^ 255140235538 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_475476899041352498020873687 : Nat.Prime 475476899041352498020873687 := by
  apply lucas_primality 475476899041352498020873687 (5 : ZMod 475476899041352498020873687)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1951, 1), (9901, 1), (24917, 1), (18293785381727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1951, 1), (9901, 1), (24917, 1), (18293785381727, 1)] : List FactorBlock).map factorBlockValue).prod) = 475476899041352498020873687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_1951
      · exact prime_oneHundredElevenDE_9901
      · exact prime_oneHundredElevenDE_24917
      · exact prime_oneHundredElevenDE_18293785381727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 475476899041352498020873687) ^ 237738449520676249010436843 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 158492299680450832673624562 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 243709328058099691450986 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 48023118780057822242286 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 19082429628019123410558 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 25991170723818 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_1682456719684785762227706893 : Nat.Prime 1682456719684785762227706893 := by
  apply lucas_primality 1682456719684785762227706893 (3 : ZMod 1682456719684785762227706893)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (16462021, 1), (393024829, 1), (3421583713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (16462021, 1), (393024829, 1), (3421583713, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682456719684785762227706893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_16462021
      · exact prime_oneHundredElevenDE_393024829
      · exact prime_oneHundredElevenDE_3421583713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1682456719684785762227706893) ^ 841228359842392881113853446 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682456719684785762227706893) ^ 88550353667620303275142468 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682456719684785762227706893) ^ 102202318882036765852 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682456719684785762227706893) ^ 4280789903186461948 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682456719684785762227706893) ^ 491718707127475084 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_4233278197916557724314875409 : Nat.Prime 4233278197916557724314875409 := by
  apply lucas_primality 4233278197916557724314875409 (11 : ZMod 4233278197916557724314875409)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (9434767, 1), (9347691976911383813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (9434767, 1), (9347691976911383813, 1)] : List FactorBlock).map factorBlockValue).prod) = 4233278197916557724314875409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_9434767
      · exact prime_oneHundredElevenDE_9347691976911383813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4233278197916557724314875409) ^ 2116639098958278862157437704 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 4233278197916557724314875409) ^ 1411092732638852574771625136 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 4233278197916557724314875409) ^ 448689214891746423024 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (11 : ZMod 4233278197916557724314875409) ^ 452868816 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_5965073824336967702443688077 : Nat.Prime 5965073824336967702443688077 := by
  apply lucas_primality 5965073824336967702443688077 (2 : ZMod 5965073824336967702443688077)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (379, 1), (24746825576811568437479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (379, 1), (24746825576811568437479, 1)] : List FactorBlock).map factorBlockValue).prod) = 5965073824336967702443688077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_53
      · exact prime_oneHundredElevenDE_379
      · exact prime_oneHundredElevenDE_24746825576811568437479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5965073824336967702443688077) ^ 2982536912168483851221844038 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5965073824336967702443688077) ^ 1988357941445655900814562692 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5965073824336967702443688077) ^ 112548562723339013253654492 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5965073824336967702443688077) ^ 15738981066852157526236644 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5965073824336967702443688077) ^ 241044 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_16403953016926661181720142207 : Nat.Prime 16403953016926661181720142207 := by
  apply lucas_primality 16403953016926661181720142207 (3 : ZMod 16403953016926661181720142207)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (9434767, 1), (9347691976911383813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (9434767, 1), (9347691976911383813, 1)] : List FactorBlock).map factorBlockValue).prod) = 16403953016926661181720142207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_31
      · exact prime_oneHundredElevenDE_9434767
      · exact prime_oneHundredElevenDE_9347691976911383813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16403953016926661181720142207) ^ 8201976508463330590860071103 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 16403953016926661181720142207) ^ 5467984338975553727240047402 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 16403953016926661181720142207) ^ 529159774739569715539359426 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 16403953016926661181720142207) ^ 1738670707705517389218 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (3 : ZMod 16403953016926661181720142207) ^ 1754866662 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_18747374876487612779108733947 : Nat.Prime 18747374876487612779108733947 := by
  apply lucas_primality 18747374876487612779108733947 (2 : ZMod 18747374876487612779108733947)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (523, 1), (937, 1), (406978372170460868209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (523, 1), (937, 1), (406978372170460868209, 1)] : List FactorBlock).map factorBlockValue).prod) = 18747374876487612779108733947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_47
      · exact prime_oneHundredElevenDE_523
      · exact prime_oneHundredElevenDE_937
      · exact prime_oneHundredElevenDE_406978372170460868209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18747374876487612779108733947) ^ 9373687438243806389554366973 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 18747374876487612779108733947) ^ 398880316521013037853377318 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 18747374876487612779108733947) ^ 35845841064029852350112302 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 18747374876487612779108733947) ^ 20007870732644197202890858 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 18747374876487612779108733947) ^ 46064794 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_32807906033853322363440284411 : Nat.Prime 32807906033853322363440284411 := by
  apply lucas_primality 32807906033853322363440284411 (2 : ZMod 32807906033853322363440284411)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (941, 1), (2917, 1), (7589, 1), (24841, 1), (152563, 1), (500693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (941, 1), (2917, 1), (7589, 1), (24841, 1), (152563, 1), (500693, 1)] : List FactorBlock).map factorBlockValue).prod) = 32807906033853322363440284411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_83
      · exact prime_oneHundredElevenDE_941
      · exact prime_oneHundredElevenDE_2917
      · exact prime_oneHundredElevenDE_7589
      · exact prime_oneHundredElevenDE_24841
      · exact prime_oneHundredElevenDE_152563
      · exact prime_oneHundredElevenDE_500693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32807906033853322363440284411) ^ 16403953016926661181720142205 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32807906033853322363440284411) ^ 6561581206770664472688056882 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32807906033853322363440284411) ^ 395275976311485811607714270 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32807906033853322363440284411) ^ 34864937336719789971775010 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32807906033853322363440284411) ^ 11247139538516737183215730 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32807906033853322363440284411) ^ 4323086840671145389832690 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32807906033853322363440284411) ^ 1320715995082859883396010 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32807906033853322363440284411) ^ 215044971807406267335070 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32807906033853322363440284411) ^ 65524994425432994596370 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_43743874711804429817920379207 : Nat.Prime 43743874711804429817920379207 := by
  apply lucas_primality 43743874711804429817920379207 (5 : ZMod 43743874711804429817920379207)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (3066433510013, 1), (419570339988143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (3066433510013, 1), (419570339988143, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804429817920379207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_17
      · exact prime_oneHundredElevenDE_3066433510013
      · exact prime_oneHundredElevenDE_419570339988143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43743874711804429817920379207) ^ 21871937355902214908960189603 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 43743874711804429817920379207) ^ 2573169100694378224583551718 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 43743874711804429817920379207) ^ 14265391559596862 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 43743874711804429817920379207) ^ 104258739340442 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_131231624135413289453761137691 : Nat.Prime 131231624135413289453761137691 := by
  apply lucas_primality 131231624135413289453761137691 (14 : ZMod 131231624135413289453761137691)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (18757, 1), (251857, 1), (48735591754852333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (18757, 1), (251857, 1), (48735591754852333, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_5
      · exact prime_oneHundredElevenDE_19
      · exact prime_oneHundredElevenDE_18757
      · exact prime_oneHundredElevenDE_251857
      · exact prime_oneHundredElevenDE_48735591754852333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 131231624135413289453761137691) ^ 65615812067706644726880568845 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 131231624135413289453761137691) ^ 43743874711804429817920379230 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 131231624135413289453761137691) ^ 26246324827082657890752227538 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 131231624135413289453761137691) ^ 6906927586074383655461112510 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 131231624135413289453761137691) ^ 6996407961583051098457170 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 131231624135413289453761137691) ^ 521056091891086169746170 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (14 : ZMod 131231624135413289453761137691) ^ 2692726596930 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem prime_oneHundredElevenDE_131231624135413289453761137697 : Nat.Prime 131231624135413289453761137697 := by
  apply lucas_primality 131231624135413289453761137697 (5 : ZMod 131231624135413289453761137697)
  · rw [← oneHundredElevenDEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (21563639, 1), (21131190407207992303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (21563639, 1), (21131190407207992303, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredElevenDE_2
      · exact prime_oneHundredElevenDE_3
      · exact prime_oneHundredElevenDE_21563639
      · exact prime_oneHundredElevenDE_21131190407207992303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 131231624135413289453761137697) ^ 65615812067706644726880568848 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 131231624135413289453761137697) ^ 43743874711804429817920379232 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 131231624135413289453761137697) ^ 6085782837275901783264 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide
    · change (5 : ZMod 131231624135413289453761137697) ^ 6210328032 ≠ 1
      rw [← oneHundredElevenDEFastPow_eq_pow]
      decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137600 : Nat.totient 131231624135413289453761137600 = 34049087556049349416194048000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (37, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_37, prime_oneHundredElevenDE_171401, prime_oneHundredElevenDE_714027719, prime_oneHundredElevenDE_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137601 : Nat.totient 131231624135413289453761137601 = 105867324026049557353750290432 := by
  rw [← show ((([(7, 1), (17, 3), (652507, 1), (2494469, 1), (2344392986017, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_17, prime_oneHundredElevenDE_652507, prime_oneHundredElevenDE_2494469, prime_oneHundredElevenDE_2344392986017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137602 : Nat.totient 131231624135413289453761137602 = 58905968455724911549783687296 := by
  rw [← show ((([(2, 1), (13, 1), (43, 1), (233, 1), (503779834220416936488983, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_13, prime_oneHundredElevenDE_43, prime_oneHundredElevenDE_233, prime_oneHundredElevenDE_503779834220416936488983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137603 : Nat.totient 131231624135413289453761137603 = 87451845126397398521289676800 := by
  rw [← show ((([(3, 1), (2729, 1), (22741, 1), (2769784141, 1), (254482680649, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_2729, prime_oneHundredElevenDE_22741, prime_oneHundredElevenDE_2769784141, prime_oneHundredElevenDE_254482680649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137604 : Nat.totient 131231624135413289453761137604 = 65011984549187603878277521920 := by
  rw [← show ((([(2, 2), (223, 1), (307, 1), (727, 1), (8963, 1), (73544037168527441, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_223, prime_oneHundredElevenDE_307, prime_oneHundredElevenDE_727, prime_oneHundredElevenDE_8963, prime_oneHundredElevenDE_73544037168527441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137605 : Nat.totient 131231624135413289453761137605 = 103255028027898722146475679744 := by
  rw [← show ((([(5, 1), (97, 1), (167, 1), (4007, 1), (404353262509829014897, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_97, prime_oneHundredElevenDE_167, prime_oneHundredElevenDE_4007, prime_oneHundredElevenDE_404353262509829014897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137606 : Nat.totient 131231624135413289453761137606 = 38801394324850313190121326720 := by
  rw [← show ((([(2, 1), (3, 3), (11, 1), (79, 1), (103, 1), (479, 1), (5924987, 1), (9566758866199, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_79, prime_oneHundredElevenDE_103, prime_oneHundredElevenDE_479, prime_oneHundredElevenDE_5924987, prime_oneHundredElevenDE_9566758866199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137607 : Nat.totient 131231624135413289453761137607 = 131195601180529653664086826560 := by
  rw [← show ((([(3643, 1), (969848975609, 1), (37142849712461, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3643, prime_oneHundredElevenDE_969848975609, prime_oneHundredElevenDE_37142849712461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137608 : Nat.totient 131231624135413289453761137608 = 56072127918899303231076080640 := by
  rw [← show ((([(2, 3), (7, 2), (331, 1), (695207, 1), (213577093, 1), (6811701929, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_331, prime_oneHundredElevenDE_695207, prime_oneHundredElevenDE_213577093, prime_oneHundredElevenDE_6811701929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137609 : Nat.totient 131231624135413289453761137609 = 86878770153352249333671051264 := by
  rw [← show ((([(3, 1), (197, 1), (577, 1), (6197, 1), (50411887, 1), (1231858315333, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_197, prime_oneHundredElevenDE_577, prime_oneHundredElevenDE_6197, prime_oneHundredElevenDE_50411887, prime_oneHundredElevenDE_1231858315333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137610 : Nat.totient 131231624135413289453761137610 = 52351918689945033433564763328 := by
  rw [← show ((([(2, 1), (5, 1), (373, 1), (35182741055070586984922557, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_373, prime_oneHundredElevenDE_35182741055070586984922557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137611 : Nat.totient 131231624135413289453761137611 = 130082654299868108349215874624 := by
  rw [← show ((([(127, 1), (1223, 1), (14153, 1), (59698005142953515147, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_127, prime_oneHundredElevenDE_1223, prime_oneHundredElevenDE_14153, prime_oneHundredElevenDE_59698005142953515147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137612 : Nat.totient 131231624135413289453761137612 = 41841967115639019825836884368 := by
  rw [← show ((([(2, 2), (3, 1), (23, 1), (475476899041352498020873687, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_23, prime_oneHundredElevenDE_475476899041352498020873687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137613 : Nat.totient 131231624135413289453761137613 = 131231103979784178010758290080 := by
  rw [← show ((([(252293, 1), (520155629111443002595241, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_252293, prime_oneHundredElevenDE_520155629111443002595241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137614 : Nat.totient 131231624135413289453761137614 = 61745150531045156301768335904 := by
  rw [← show ((([(2, 1), (19, 1), (149, 1), (79636439, 1), (291042764346141823, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_19, prime_oneHundredElevenDE_149, prime_oneHundredElevenDE_79636439, prime_oneHundredElevenDE_291042764346141823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137615 : Nat.totient 131231624135413289453761137615 = 55376861173529181712680395520 := by
  rw [← show ((([(3, 2), (5, 1), (7, 1), (13, 1), (584409528191, 1), (54836194679887, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_13, prime_oneHundredElevenDE_584409528191, prime_oneHundredElevenDE_54836194679887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137616 : Nat.totient 131231624135413289453761137616 = 63146307325180328297102476800 := by
  rw [← show ((([(2, 4), (29, 1), (359, 1), (3079, 1), (6379, 1), (40111027163996851, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_29, prime_oneHundredElevenDE_359, prime_oneHundredElevenDE_3079, prime_oneHundredElevenDE_6379, prime_oneHundredElevenDE_40111027163996851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137617 : Nat.totient 131231624135413289453761137617 = 115447424824303099922249856000 := by
  rw [← show ((([(11, 2), (31, 1), (20593, 1), (10978921, 1), (154743408951839, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_31, prime_oneHundredElevenDE_20593, prime_oneHundredElevenDE_10978921, prime_oneHundredElevenDE_154743408951839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137618 : Nat.totient 131231624135413289453761137618 = 41170705611096527216584886528 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (3066433510013, 1), (419570339988143, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_17, prime_oneHundredElevenDE_3066433510013, prime_oneHundredElevenDE_419570339988143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137619 : Nat.totient 131231624135413289453761137619 = 126789797770734595914411426432 := by
  rw [← show ((([(53, 1), (67, 1), (3109, 1), (39163, 1), (303522685959904907, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_53, prime_oneHundredElevenDE_67, prime_oneHundredElevenDE_3109, prime_oneHundredElevenDE_39163, prime_oneHundredElevenDE_303522685959904907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137620 : Nat.totient 131231624135413289453761137620 = 52492463161140804286335371520 := by
  rw [← show ((([(2, 2), (5, 1), (287579, 1), (13255499, 1), (1721294803250761, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_287579, prime_oneHundredElevenDE_13255499, prime_oneHundredElevenDE_1721294803250761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137621 : Nat.totient 131231624135413289453761137621 = 87487749423608859635840758412 := by
  rw [← show ((([(3, 1), (43743874711804429817920379207, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_43743874711804429817920379207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137622 : Nat.totient 131231624135413289453761137622 = 54881600001080709359377345536 := by
  rw [← show ((([(2, 1), (7, 1), (47, 1), (523, 1), (937, 1), (406978372170460868209, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_47, prime_oneHundredElevenDE_523, prime_oneHundredElevenDE_937, prime_oneHundredElevenDE_406978372170460868209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137623 : Nat.totient 131231624135413289453761137623 = 131231620477126112949132320448 := by
  rw [← show ((([(35991283, 1), (11238561589, 1), (324437051129, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_35991283, prime_oneHundredElevenDE_11238561589, prime_oneHundredElevenDE_324437051129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137624 : Nat.totient 131231624135413289453761137624 = 43022755256061933021696998400 := by
  rw [← show ((([(2, 3), (3, 2), (61, 1), (11909, 1), (109253, 1), (22965055844998711, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_61, prime_oneHundredElevenDE_11909, prime_oneHundredElevenDE_109253, prime_oneHundredElevenDE_22965055844998711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137625 : Nat.totient 131231624135413289453761137625 = 103805379768515206629754368000 := by
  rw [← show ((([(5, 3), (89, 1), (336491, 1), (110407393, 1), (317516922143, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_89, prime_oneHundredElevenDE_336491, prime_oneHundredElevenDE_110407393, prime_oneHundredElevenDE_317516922143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137626 : Nat.totient 131231624135413289453761137626 = 65615714935467895576387874496 := by
  rw [← show ((([(2, 1), (691267, 1), (29674847, 1), (3198705040998737, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_691267, prime_oneHundredElevenDE_29674847, prime_oneHundredElevenDE_3198705040998737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137627 : Nat.totient 131231624135413289453761137627 = 86004879102875720506691607072 := by
  rw [← show ((([(3, 1), (59, 1), (3172423, 1), (233708306012414121437, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_59, prime_oneHundredElevenDE_3172423, prime_oneHundredElevenDE_233708306012414121437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137628 : Nat.totient 131231624135413289453761137628 = 53718787646345917849707110400 := by
  rw [← show ((([(2, 2), (11, 1), (13, 1), (41, 1), (119033, 1), (47010106916580133433, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_13, prime_oneHundredElevenDE_41, prime_oneHundredElevenDE_119033, prime_oneHundredElevenDE_47010106916580133433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137629 : Nat.totient 131231624135413289453761137629 = 112484249258925676674652403676 := by
  rw [← show ((([(7, 1), (18747374876487612779108733947, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_18747374876487612779108733947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137630 : Nat.totient 131231624135413289453761137630 = 34981692148969777444609811456 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (4373, 1), (6473, 1), (154536888817040220149, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_4373, prime_oneHundredElevenDE_6473, prime_oneHundredElevenDE_154536888817040220149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137631 : Nat.totient 131231624135413289453761137631 = 131107466161958221132399016640 := by
  rw [← show ((([(1061, 1), (278219, 1), (444566091453594151609, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_1061, prime_oneHundredElevenDE_278219, prime_oneHundredElevenDE_444566091453594151609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137632 : Nat.totient 131231624135413289453761137632 = 65615808200024016787022817664 := by
  rw [← show ((([(2, 5), (16965149, 1), (241730164246224144299, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_16965149, prime_oneHundredElevenDE_241730164246224144299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137633 : Nat.totient 131231624135413289453761137633 = 82875594600738013432534083072 := by
  rw [← show ((([(3, 3), (19, 1), (12277, 1), (105529, 1), (197449964515277477, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_19, prime_oneHundredElevenDE_12277, prime_oneHundredElevenDE_105529, prime_oneHundredElevenDE_197449964515277477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137634 : Nat.totient 131231624135413289453761137634 = 65615811712825008644833561920 := by
  rw [← show ((([(2, 1), (184894921, 1), (354881636081862111977, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_184894921, prime_oneHundredElevenDE_354881636081862111977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137635 : Nat.totient 131231624135413289453761137635 = 94501892127064795044281077248 := by
  rw [← show ((([(5, 1), (17, 1), (23, 1), (8059, 1), (8329339924667678775283, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_17, prime_oneHundredElevenDE_23, prime_oneHundredElevenDE_8059, prime_oneHundredElevenDE_8329339924667678775283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137636 : Nat.totient 131231624135413289453761137636 = 37122336768386105973376413696 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (109, 1), (1307, 1), (54702140897, 1), (200471577739, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_109, prime_oneHundredElevenDE_1307, prime_oneHundredElevenDE_54702140897, prime_oneHundredElevenDE_200471577739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137637 : Nat.totient 131231624135413289453761137637 = 127680728001708821759915319936 := by
  rw [← show ((([(37, 2), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_37, prime_oneHundredElevenDE_31177, prime_oneHundredElevenDE_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137638 : Nat.totient 131231624135413289453761137638 = 65513447306290565717946277120 := by
  rw [← show ((([(2, 1), (641, 1), (102364761416079008934291059, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_641, prime_oneHundredElevenDE_102364761416079008934291059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137639 : Nat.totient 131231624135413289453761137639 = 79532786060498002747980714560 := by
  rw [← show ((([(3, 1), (11, 1), (51929, 1), (76579866411664230037727, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_51929, prime_oneHundredElevenDE_76579866411664230037727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137640 : Nat.totient 131231624135413289453761137640 = 51777985288716624973735526400 := by
  rw [← show ((([(2, 3), (5, 1), (83, 1), (941, 1), (2917, 1), (7589, 1), (24841, 1), (152563, 1), (500693, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_83, prime_oneHundredElevenDE_941, prime_oneHundredElevenDE_2917, prime_oneHundredElevenDE_7589, prime_oneHundredElevenDE_24841, prime_oneHundredElevenDE_152563, prime_oneHundredElevenDE_500693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137641 : Nat.totient 131231624135413289453761137641 = 121126162790327204796769626192 := by
  rw [← show ((([(13, 1), (11299, 1), (893418914780840302094543, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_13, prime_oneHundredElevenDE_11299, prime_oneHundredElevenDE_893418914780840302094543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137642 : Nat.totient 131231624135413289453761137642 = 43743225104968691175679699560 := by
  rw [← show ((([(2, 1), (3, 2), (67339, 1), (108267805956440373379271, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_67339, prime_oneHundredElevenDE_108267805956440373379271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137643 : Nat.totient 131231624135413289453761137643 = 112484245264880823309097743720 := by
  rw [← show ((([(7, 1), (28162991, 1), (665674142227564280339, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_28162991, prime_oneHundredElevenDE_665674142227564280339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137644 : Nat.totient 131231624135413289453761137644 = 65615812067706644726880568820 := by
  rw [← show ((([(2, 2), (32807906033853322363440284411, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_32807906033853322363440284411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137645 : Nat.totient 131231624135413289453761137645 = 66005192176946643050344733952 := by
  rw [← show ((([(3, 1), (5, 1), (29, 1), (43, 1), (6293333183, 1), (1114807973630243, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_29, prime_oneHundredElevenDE_43, prime_oneHundredElevenDE_6293333183, prime_oneHundredElevenDE_1114807973630243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137646 : Nat.totient 131231624135413289453761137646 = 65615721544034659181454772368 := by
  rw [← show ((([(2, 1), (724847, 1), (90523671985545425071609, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_724847, prime_oneHundredElevenDE_90523671985545425071609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137647 : Nat.totient 131231624135413289453761137647 = 131231622601822054655100524496 := by
  rw [← show ((([(85571449, 1), (1533591234798575041703, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_85571449, prime_oneHundredElevenDE_1533591234798575041703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137648 : Nat.totient 131231624135413289453761137648 = 42332777492273428321155836160 := by
  rw [← show ((([(2, 4), (3, 1), (31, 1), (9434767, 1), (9347691976911383813, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_31, prime_oneHundredElevenDE_9434767, prime_oneHundredElevenDE_9347691976911383813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137649 : Nat.totient 131231624135413289453761137649 = 130272446976988989408497510400 := by
  rw [← show ((([(151, 1), (1447, 1), (66529873, 1), (9027683626564129, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_151, prime_oneHundredElevenDE_1447, prime_oneHundredElevenDE_66529873, prime_oneHundredElevenDE_9027683626564129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137650 : Nat.totient 131231624135413289453761137650 = 40903362214582318083323040000 := by
  rw [← show ((([(2, 1), (5, 2), (7, 1), (11, 1), (68887661, 1), (74045339, 1), (6682494491, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_68887661, prime_oneHundredElevenDE_74045339, prime_oneHundredElevenDE_6682494491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137651 : Nat.totient 131231624135413289453761137651 = 87487749144066499268656008960 := by
  rw [← show ((([(3, 2), (312967771, 1), (46590393394217823809, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_312967771, prime_oneHundredElevenDE_46590393394217823809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137652 : Nat.totient 131231624135413289453761137652 = 58431010750984886477688576000 := by
  rw [← show ((([(2, 2), (17, 1), (19, 1), (1031, 1), (4967, 1), (9403, 1), (2109389251383101, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_17, prime_oneHundredElevenDE_19, prime_oneHundredElevenDE_1031, prime_oneHundredElevenDE_4967, prime_oneHundredElevenDE_9403, prime_oneHundredElevenDE_2109389251383101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137653 : Nat.totient 131231624135413289453761137653 = 131231529701957263889983626720 := by
  rw [← show ((([(1389673, 1), (94433456025563776121261, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_1389673, prime_oneHundredElevenDE_94433456025563776121261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137654 : Nat.totient 131231624135413289453761137654 = 40378961272434858293464965408 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (1682456719684785762227706893, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_13, prime_oneHundredElevenDE_1682456719684785762227706893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137655 : Nat.totient 131231624135413289453761137655 = 104985298247202483394285012128 := by
  rw [← show ((([(5, 1), (98937437, 1), (265282037042082037063, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_98937437, prime_oneHundredElevenDE_265282037042082037063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137656 : Nat.totient 131231624135413289453761137656 = 65615812067706644726880568824 := by
  rw [← show ((([(2, 3), (16403953016926661181720142207, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_16403953016926661181720142207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137657 : Nat.totient 131231624135413289453761137657 = 74989499505902345449526430528 := by
  rw [← show ((([(3, 1), (7, 2), (1563116036107, 1), (571123394779433, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_1563116036107, prime_oneHundredElevenDE_571123394779433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137658 : Nat.totient 131231624135413289453761137658 = 61089950532977337837317760000 := by
  rw [← show ((([(2, 1), (23, 1), (71, 1), (101, 1), (389, 1), (3343, 1), (106181, 1), (2881165199599, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_23, prime_oneHundredElevenDE_71, prime_oneHundredElevenDE_101, prime_oneHundredElevenDE_389, prime_oneHundredElevenDE_3343, prime_oneHundredElevenDE_106181, prime_oneHundredElevenDE_2881165199599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137659 : Nat.totient 131231624135413289453761137659 = 131156505861723871428887775216 := by
  rw [← show ((([(1747, 1), (75118273689418024873360697, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_1747, prime_oneHundredElevenDE_75118273689418024873360697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137660 : Nat.totient 131231624135413289453761137660 = 34995099769443543854336302944 := by
  rw [← show ((([(2, 2), (3, 4), (5, 1), (81007175392230425588741443, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_81007175392230425588741443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137661 : Nat.totient 131231624135413289453761137661 = 117641445020566711998099696000 := by
  rw [← show ((([(11, 1), (73, 1), (4567, 1), (36421237591, 1), (982510607471, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_73, prime_oneHundredElevenDE_4567, prime_oneHundredElevenDE_36421237591, prime_oneHundredElevenDE_982510607471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137662 : Nat.totient 131231624135413289453761137662 = 65505842968523138023574632320 := by
  rw [← show ((([(2, 1), (787, 1), (2539, 1), (83537, 1), (393090184979942591, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_787, prime_oneHundredElevenDE_2539, prime_oneHundredElevenDE_83537, prime_oneHundredElevenDE_393090184979942591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137663 : Nat.totient 131231624135413289453761137663 = 87487408537734133909326510240 := by
  rw [← show ((([(3, 1), (267647, 1), (6245311, 1), (26169823839032213, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_267647, prime_oneHundredElevenDE_6245311, prime_oneHundredElevenDE_26169823839032213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137664 : Nat.totient 131231624135413289453761137664 = 56174117223623100927000416256 := by
  rw [← show ((([(2, 10), (7, 1), (827, 1), (22137827421789521589599, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_827, prime_oneHundredElevenDE_22137827421789521589599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137665 : Nat.totient 131231624135413289453761137665 = 104985282664712108469165752320 := by
  rw [← show ((([(5, 1), (6307841, 1), (4160904630773454481613, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_6307841, prime_oneHundredElevenDE_4160904630773454481613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137666 : Nat.totient 131231624135413289453761137666 = 43517047031684791480632987648 := by
  rw [← show ((([(2, 1), (3, 1), (193, 1), (247997, 1), (12112361333, 1), (37727210827, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_193, prime_oneHundredElevenDE_247997, prime_oneHundredElevenDE_12112361333, prime_oneHundredElevenDE_37727210827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137667 : Nat.totient 131231624135413289453761137667 = 121136882452626075535436839392 := by
  rw [← show ((([(13, 1), (88765877, 1), (113723208278657738867, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_13, prime_oneHundredElevenDE_88765877, prime_oneHundredElevenDE_113723208278657738867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137668 : Nat.totient 131231624135413289453761137668 = 65163911398129142979094915200 := by
  rw [← show ((([(2, 2), (157, 1), (3331, 1), (4943, 1), (54011, 1), (234980270081387, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_157, prime_oneHundredElevenDE_3331, prime_oneHundredElevenDE_4943, prime_oneHundredElevenDE_54011, prime_oneHundredElevenDE_234980270081387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137669 : Nat.totient 131231624135413289453761137669 = 78495608764875216017867304960 := by
  rw [← show ((([(3, 2), (17, 1), (41, 1), (47, 1), (613, 1), (726114122709561931823, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_17, prime_oneHundredElevenDE_41, prime_oneHundredElevenDE_47, prime_oneHundredElevenDE_613, prime_oneHundredElevenDE_726114122709561931823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137670 : Nat.totient 131231624135413289453761137670 = 52302547534996562907967395840 := by
  rw [← show ((([(2, 1), (5, 1), (277, 1), (87473, 1), (1542673981, 1), (351083612567, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_277, prime_oneHundredElevenDE_87473, prime_oneHundredElevenDE_1542673981, prime_oneHundredElevenDE_351083612567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137671 : Nat.totient 131231624135413289453761137671 = 106045603360241692026899617920 := by
  rw [← show ((([(7, 1), (19, 1), (211, 1), (7927, 1), (6439451269, 1), (91610802659, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_19, prime_oneHundredElevenDE_211, prime_oneHundredElevenDE_7927, prime_oneHundredElevenDE_6439451269, prime_oneHundredElevenDE_91610802659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137672 : Nat.totient 131231624135413289453761137672 = 38913888283024655136565405440 := by
  rw [← show ((([(2, 3), (3, 1), (11, 1), (53, 1), (379, 1), (24746825576811568437479, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_53, prime_oneHundredElevenDE_379, prime_oneHundredElevenDE_24746825576811568437479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137673 : Nat.totient 131231624135413289453761137673 = 130859693891693814220830496224 := by
  rw [← show ((([(587, 1), (883, 1), (253186006616388858359513, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_587, prime_oneHundredElevenDE_883, prime_oneHundredElevenDE_253186006616388858359513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137674 : Nat.totient 131231624135413289453761137674 = 60959384087675759852610060288 := by
  rw [← show ((([(2, 1), (29, 1), (37, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_29, prime_oneHundredElevenDE_37, prime_oneHundredElevenDE_113, prime_oneHundredElevenDE_449, prime_oneHundredElevenDE_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137675 : Nat.totient 131231624135413289453761137675 = 69840316332600913727232480000 := by
  rw [← show ((([(3, 1), (5, 2), (467, 1), (6203251, 1), (604005656150070457, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_467, prime_oneHundredElevenDE_6203251, prime_oneHundredElevenDE_604005656150070457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137676 : Nat.totient 131231624135413289453761137676 = 65615439954647445900541828688 := by
  rw [← show ((([(2, 2), (176333, 1), (186056529599413169193743, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_176333, prime_oneHundredElevenDE_186056529599413169193743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137677 : Nat.totient 131231624135413289453761137677 = 131220067108418897920787423584 := by
  rw [← show ((([(11987, 1), (215399, 1), (50825810824775294729, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_11987, prime_oneHundredElevenDE_215399, prime_oneHundredElevenDE_50825810824775294729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137678 : Nat.totient 131231624135413289453761137678 = 37396850051642100955795021824 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (383, 1), (17135687, 1), (158696615200507393, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_383, prime_oneHundredElevenDE_17135687, prime_oneHundredElevenDE_158696615200507393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137679 : Nat.totient 131231624135413289453761137679 = 126998345937496731729446262240 := by
  rw [← show ((([(31, 1), (4233278197916557724314875409, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_31, prime_oneHundredElevenDE_4233278197916557724314875409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137680 : Nat.totient 131231624135413289453761137680 = 48420940021320349261332455424 := by
  rw [← show ((([(2, 4), (5, 1), (13, 1), (1433, 1), (88056004170522632356649, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_13, prime_oneHundredElevenDE_1433, prime_oneHundredElevenDE_88056004170522632356649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137681 : Nat.totient 131231624135413289453761137681 = 83683333627442399293391769216 := by
  rw [← show ((([(3, 1), (23, 1), (139333, 1), (13650087173644506269753, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_23, prime_oneHundredElevenDE_139333, prime_oneHundredElevenDE_13650087173644506269753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137682 : Nat.totient 131231624135413289453761137682 = 65060383860860647622322960000 := by
  rw [← show ((([(2, 1), (131, 1), (1499, 1), (9001, 1), (16787, 1), (2211422517566347, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_131, prime_oneHundredElevenDE_1499, prime_oneHundredElevenDE_9001, prime_oneHundredElevenDE_16787, prime_oneHundredElevenDE_2211422517566347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137683 : Nat.totient 131231624135413289453761137683 = 119301419273178407378833188000 := by
  rw [← show ((([(11, 1), (2433853, 1), (14556011, 1), (336751159161191, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_2433853, prime_oneHundredElevenDE_14556011, prime_oneHundredElevenDE_336751159161191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137684 : Nat.totient 131231624135413289453761137684 = 43551170417919828805506632160 := by
  rw [← show ((([(2, 2), (3, 1), (227, 1), (48176073471150253103436541, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_227, prime_oneHundredElevenDE_48176073471150253103436541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137685 : Nat.totient 131231624135413289453761137685 = 87352826582045949084619879680 := by
  rw [← show ((([(5, 1), (7, 1), (61, 1), (79, 1), (2243, 1), (346883992808737608223, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_61, prime_oneHundredElevenDE_79, prime_oneHundredElevenDE_2243, prime_oneHundredElevenDE_346883992808737608223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137686 : Nat.totient 131231624135413289453761137686 = 59472831308508825278236577280 := by
  rw [← show ((([(2, 1), (17, 1), (59, 1), (67, 1), (181, 1), (5394537264573611952703, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_17, prime_oneHundredElevenDE_59, prime_oneHundredElevenDE_67, prime_oneHundredElevenDE_181, prime_oneHundredElevenDE_5394537264573611952703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137687 : Nat.totient 131231624135413289453761137687 = 87479146045752275029720421952 := by
  rw [← show ((([(3, 3), (10169, 1), (477965436476922562230749, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_10169, prime_oneHundredElevenDE_477965436476922562230749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137688 : Nat.totient 131231624135413289453761137688 = 64051950307274992900984043520 := by
  rw [← show ((([(2, 3), (43, 1), (1787, 1), (31277, 1), (356019271, 1), (19171536113, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_43, prime_oneHundredElevenDE_1787, prime_oneHundredElevenDE_31277, prime_oneHundredElevenDE_356019271, prime_oneHundredElevenDE_19171536113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137689 : Nat.totient 131231624135413289453761137689 = 130005160062166916247949450560 := by
  rw [← show ((([(107, 1), (438791707, 1), (2795093337911418961, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_107, prime_oneHundredElevenDE_438791707, prime_oneHundredElevenDE_2795093337911418961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137690 : Nat.totient 131231624135413289453761137690 = 33151353271361456822952357888 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (19, 1), (18757, 1), (251857, 1), (48735591754852333, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_19, prime_oneHundredElevenDE_18757, prime_oneHundredElevenDE_251857, prime_oneHundredElevenDE_48735591754852333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137691 : Nat.totient 131231624135413289453761137691 = 131231624135413289453761137690 := by
  rw [← show ((([(131231624135413289453761137691, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_131231624135413289453761137691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137692 : Nat.totient 131231624135413289453761137692 = 56242124625473180085153531888 := by
  rw [← show ((([(2, 2), (7, 1), (14096978603, 1), (332471506917410563, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_14096978603, prime_oneHundredElevenDE_332471506917410563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137693 : Nat.totient 131231624135413289453761137693 = 80712725010628154300980704000 := by
  rw [← show ((([(3, 1), (13, 1), (1789, 1), (1437251, 1), (1308672380247113533, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_13, prime_oneHundredElevenDE_1789, prime_oneHundredElevenDE_1437251, prime_oneHundredElevenDE_1308672380247113533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137694 : Nat.totient 131231624135413289453761137694 = 59650738243369677024436880760 := by
  rw [← show ((([(2, 1), (11, 1), (5965073824336967702443688077, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_11, prime_oneHundredElevenDE_5965073824336967702443688077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137695 : Nat.totient 131231624135413289453761137695 = 104985299308323577759398655840 := by
  rw [← show ((([(5, 1), (15011284666871, 1), (1748439617896709, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_15011284666871, prime_oneHundredElevenDE_1748439617896709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137696 : Nat.totient 131231624135413289453761137696 = 43743872683210150723883008896 := by
  rw [← show ((([(2, 5), (3, 2), (21563639, 1), (21131190407207992303, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_21563639, prime_oneHundredElevenDE_21131190407207992303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137697 : Nat.totient 131231624135413289453761137697 = 131231624135413289453761137696 := by
  rw [← show ((([(131231624135413289453761137697, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_131231624135413289453761137697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137698 : Nat.totient 131231624135413289453761137698 = 65615812067669700771325707264 := by
  rw [← show ((([(2, 1), (1776175990993, 1), (36942179378870593, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_1776175990993, prime_oneHundredElevenDE_36942179378870593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137699 : Nat.totient 131231624135413289453761137699 = 74968602630656630530436186112 := by
  rw [← show ((([(3, 1), (7, 1), (3617, 1), (456119, 1), (3787847943891692353, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_3, prime_oneHundredElevenDE_7, prime_oneHundredElevenDE_3617, prime_oneHundredElevenDE_456119, prime_oneHundredElevenDE_3787847943891692353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137700 : Nat.totient 131231624135413289453761137700 = 52489247006232848982010644000 := by
  rw [← show ((([(2, 2), (5, 2), (15427, 1), (85066198311669987329851, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_2, prime_oneHundredElevenDE_5, prime_oneHundredElevenDE_15427, prime_oneHundredElevenDE_85066198311669987329851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredElevenDE_131231624135413289453761137701 : Nat.totient 131231624135413289453761137701 = 131196729679253616975349128000 := by
  rw [← show ((([(7013, 1), (8291, 1), (368647, 1), (6122334382059101, 1)] : List FactorBlock).map factorBlockValue).prod) = 131231624135413289453761137701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredElevenDE_7013, prime_oneHundredElevenDE_8291, prime_oneHundredElevenDE_368647, prime_oneHundredElevenDE_6122334382059101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredElevenDE : certifiedKill 1 131231624135413289453761137599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredElevenDE_131231624135413289453761137600, phi_oneHundredElevenDE_131231624135413289453761137601, phi_oneHundredElevenDE_131231624135413289453761137602,
    phi_oneHundredElevenDE_131231624135413289453761137603, phi_oneHundredElevenDE_131231624135413289453761137604, phi_oneHundredElevenDE_131231624135413289453761137605,
    phi_oneHundredElevenDE_131231624135413289453761137606, phi_oneHundredElevenDE_131231624135413289453761137607, phi_oneHundredElevenDE_131231624135413289453761137608,
    phi_oneHundredElevenDE_131231624135413289453761137609, phi_oneHundredElevenDE_131231624135413289453761137610, phi_oneHundredElevenDE_131231624135413289453761137611,
    phi_oneHundredElevenDE_131231624135413289453761137612, phi_oneHundredElevenDE_131231624135413289453761137613, phi_oneHundredElevenDE_131231624135413289453761137614,
    phi_oneHundredElevenDE_131231624135413289453761137615, phi_oneHundredElevenDE_131231624135413289453761137616, phi_oneHundredElevenDE_131231624135413289453761137617,
    phi_oneHundredElevenDE_131231624135413289453761137618, phi_oneHundredElevenDE_131231624135413289453761137619, phi_oneHundredElevenDE_131231624135413289453761137620,
    phi_oneHundredElevenDE_131231624135413289453761137621, phi_oneHundredElevenDE_131231624135413289453761137622, phi_oneHundredElevenDE_131231624135413289453761137623,
    phi_oneHundredElevenDE_131231624135413289453761137624, phi_oneHundredElevenDE_131231624135413289453761137625, phi_oneHundredElevenDE_131231624135413289453761137626,
    phi_oneHundredElevenDE_131231624135413289453761137627, phi_oneHundredElevenDE_131231624135413289453761137628, phi_oneHundredElevenDE_131231624135413289453761137629,
    phi_oneHundredElevenDE_131231624135413289453761137630, phi_oneHundredElevenDE_131231624135413289453761137631, phi_oneHundredElevenDE_131231624135413289453761137632,
    phi_oneHundredElevenDE_131231624135413289453761137633, phi_oneHundredElevenDE_131231624135413289453761137634, phi_oneHundredElevenDE_131231624135413289453761137635,
    phi_oneHundredElevenDE_131231624135413289453761137636, phi_oneHundredElevenDE_131231624135413289453761137637, phi_oneHundredElevenDE_131231624135413289453761137638,
    phi_oneHundredElevenDE_131231624135413289453761137639, phi_oneHundredElevenDE_131231624135413289453761137640, phi_oneHundredElevenDE_131231624135413289453761137641,
    phi_oneHundredElevenDE_131231624135413289453761137642, phi_oneHundredElevenDE_131231624135413289453761137643, phi_oneHundredElevenDE_131231624135413289453761137644,
    phi_oneHundredElevenDE_131231624135413289453761137645, phi_oneHundredElevenDE_131231624135413289453761137646, phi_oneHundredElevenDE_131231624135413289453761137647,
    phi_oneHundredElevenDE_131231624135413289453761137648, phi_oneHundredElevenDE_131231624135413289453761137649, phi_oneHundredElevenDE_131231624135413289453761137650,
    phi_oneHundredElevenDE_131231624135413289453761137651, phi_oneHundredElevenDE_131231624135413289453761137652, phi_oneHundredElevenDE_131231624135413289453761137653,
    phi_oneHundredElevenDE_131231624135413289453761137654, phi_oneHundredElevenDE_131231624135413289453761137655, phi_oneHundredElevenDE_131231624135413289453761137656,
    phi_oneHundredElevenDE_131231624135413289453761137657, phi_oneHundredElevenDE_131231624135413289453761137658, phi_oneHundredElevenDE_131231624135413289453761137659,
    phi_oneHundredElevenDE_131231624135413289453761137660, phi_oneHundredElevenDE_131231624135413289453761137661, phi_oneHundredElevenDE_131231624135413289453761137662,
    phi_oneHundredElevenDE_131231624135413289453761137663, phi_oneHundredElevenDE_131231624135413289453761137664, phi_oneHundredElevenDE_131231624135413289453761137665,
    phi_oneHundredElevenDE_131231624135413289453761137666, phi_oneHundredElevenDE_131231624135413289453761137667, phi_oneHundredElevenDE_131231624135413289453761137668,
    phi_oneHundredElevenDE_131231624135413289453761137669, phi_oneHundredElevenDE_131231624135413289453761137670, phi_oneHundredElevenDE_131231624135413289453761137671,
    phi_oneHundredElevenDE_131231624135413289453761137672, phi_oneHundredElevenDE_131231624135413289453761137673, phi_oneHundredElevenDE_131231624135413289453761137674,
    phi_oneHundredElevenDE_131231624135413289453761137675, phi_oneHundredElevenDE_131231624135413289453761137676, phi_oneHundredElevenDE_131231624135413289453761137677,
    phi_oneHundredElevenDE_131231624135413289453761137678, phi_oneHundredElevenDE_131231624135413289453761137679, phi_oneHundredElevenDE_131231624135413289453761137680,
    phi_oneHundredElevenDE_131231624135413289453761137681, phi_oneHundredElevenDE_131231624135413289453761137682, phi_oneHundredElevenDE_131231624135413289453761137683,
    phi_oneHundredElevenDE_131231624135413289453761137684, phi_oneHundredElevenDE_131231624135413289453761137685, phi_oneHundredElevenDE_131231624135413289453761137686,
    phi_oneHundredElevenDE_131231624135413289453761137687, phi_oneHundredElevenDE_131231624135413289453761137688, phi_oneHundredElevenDE_131231624135413289453761137689,
    phi_oneHundredElevenDE_131231624135413289453761137690, phi_oneHundredElevenDE_131231624135413289453761137691, phi_oneHundredElevenDE_131231624135413289453761137692,
    phi_oneHundredElevenDE_131231624135413289453761137693, phi_oneHundredElevenDE_131231624135413289453761137694, phi_oneHundredElevenDE_131231624135413289453761137695,
    phi_oneHundredElevenDE_131231624135413289453761137696, phi_oneHundredElevenDE_131231624135413289453761137697, phi_oneHundredElevenDE_131231624135413289453761137698,
    phi_oneHundredElevenDE_131231624135413289453761137699, phi_oneHundredElevenDE_131231624135413289453761137700, phi_oneHundredElevenDE_131231624135413289453761137701
    ]

end TotientTailPeriodKiller
end Erdos249257
