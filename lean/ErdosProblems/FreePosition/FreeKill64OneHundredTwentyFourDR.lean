import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentyFourDRFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentyFourDRFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentyFourDRFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentyFourDRFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentyFourDRFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentyFourDRFastPow a n * oneHundredTwentyFourDRFastPow a n * a else oneHundredTwentyFourDRFastPow a n * oneHundredTwentyFourDRFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentyFourDR_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentyFourDR_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentyFourDR_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentyFourDR_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentyFourDR_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentyFourDR_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentyFourDR_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentyFourDR_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentyFourDR_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentyFourDR_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentyFourDR_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentyFourDR_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentyFourDR_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentyFourDR_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentyFourDR_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentyFourDR_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentyFourDR_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentyFourDR_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentyFourDR_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentyFourDR_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentyFourDR_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentyFourDR_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentyFourDR_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentyFourDR_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentyFourDR_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentyFourDR_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentyFourDR_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentyFourDR_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentyFourDR_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentyFourDR_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentyFourDR_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentyFourDR_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentyFourDR_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentyFourDR_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentyFourDR_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentyFourDR_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentyFourDR_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentyFourDR_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentyFourDR_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwentyFourDR_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentyFourDR_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentyFourDR_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentyFourDR_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentyFourDR_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwentyFourDR_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentyFourDR_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredTwentyFourDR_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentyFourDR_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwentyFourDR_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwentyFourDR_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwentyFourDR_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentyFourDR_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredTwentyFourDR_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTwentyFourDR_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentyFourDR_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredTwentyFourDR_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwentyFourDR_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredTwentyFourDR_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredTwentyFourDR_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredTwentyFourDR_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentyFourDR_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwentyFourDR_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredTwentyFourDR_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTwentyFourDR_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentyFourDR_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredTwentyFourDR_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTwentyFourDR_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentyFourDR_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredTwentyFourDR_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTwentyFourDR_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredTwentyFourDR_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredTwentyFourDR_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredTwentyFourDR_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredTwentyFourDR_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredTwentyFourDR_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredTwentyFourDR_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTwentyFourDR_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredTwentyFourDR_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredTwentyFourDR_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredTwentyFourDR_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTwentyFourDR_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredTwentyFourDR_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredTwentyFourDR_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredTwentyFourDR_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredTwentyFourDR_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwentyFourDR_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredTwentyFourDR_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredTwentyFourDR_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredTwentyFourDR_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredTwentyFourDR_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredTwentyFourDR_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredTwentyFourDR_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredTwentyFourDR_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredTwentyFourDR_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredTwentyFourDR_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredTwentyFourDR_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredTwentyFourDR_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredTwentyFourDR_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredTwentyFourDR_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredTwentyFourDR_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3121 : Nat.Prime 3121 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3307 : Nat.Prime 3307 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3371 : Nat.Prime 3371 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3677 : Nat.Prime 3677 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4073 : Nat.Prime 4073 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4283 : Nat.Prime 4283 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4409 : Nat.Prime 4409 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4567 : Nat.Prime 4567 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5081 : Nat.Prime 5081 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5233 : Nat.Prime 5233 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5281 : Nat.Prime 5281 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5449 : Nat.Prime 5449 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5477 : Nat.Prime 5477 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5527 : Nat.Prime 5527 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5897 : Nat.Prime 5897 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6073 : Nat.Prime 6073 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6089 : Nat.Prime 6089 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6211 : Nat.Prime 6211 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6571 : Nat.Prime 6571 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6637 : Nat.Prime 6637 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6659 : Nat.Prime 6659 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6701 : Nat.Prime 6701 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6719 : Nat.Prime 6719 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6761 : Nat.Prime 6761 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6899 : Nat.Prime 6899 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7307 : Nat.Prime 7307 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7487 : Nat.Prime 7487 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7523 : Nat.Prime 7523 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7547 : Nat.Prime 7547 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7687 : Nat.Prime 7687 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7741 : Nat.Prime 7741 := by norm_num

private theorem prime_oneHundredTwentyFourDR_8219 : Nat.Prime 8219 := by norm_num

private theorem prime_oneHundredTwentyFourDR_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredTwentyFourDR_8597 : Nat.Prime 8597 := by norm_num

private theorem prime_oneHundredTwentyFourDR_8761 : Nat.Prime 8761 := by norm_num

private theorem prime_oneHundredTwentyFourDR_8803 : Nat.Prime 8803 := by norm_num

private theorem prime_oneHundredTwentyFourDR_9029 : Nat.Prime 9029 := by norm_num

private theorem prime_oneHundredTwentyFourDR_9181 : Nat.Prime 9181 := by norm_num

private theorem prime_oneHundredTwentyFourDR_9619 : Nat.Prime 9619 := by norm_num

private theorem prime_oneHundredTwentyFourDR_9833 : Nat.Prime 9833 := by norm_num

private theorem prime_oneHundredTwentyFourDR_9923 : Nat.Prime 9923 := by norm_num

private theorem prime_oneHundredTwentyFourDR_10177 : Nat.Prime 10177 := by norm_num

private theorem prime_oneHundredTwentyFourDR_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredTwentyFourDR_10861 : Nat.Prime 10861 := by norm_num

private theorem prime_oneHundredTwentyFourDR_11437 : Nat.Prime 11437 := by norm_num

private theorem prime_oneHundredTwentyFourDR_11489 : Nat.Prime 11489 := by norm_num

private theorem prime_oneHundredTwentyFourDR_12511 : Nat.Prime 12511 := by norm_num

private theorem prime_oneHundredTwentyFourDR_13513 : Nat.Prime 13513 := by norm_num

private theorem prime_oneHundredTwentyFourDR_13613 : Nat.Prime 13613 := by norm_num

private theorem prime_oneHundredTwentyFourDR_13649 : Nat.Prime 13649 := by norm_num

private theorem prime_oneHundredTwentyFourDR_13799 : Nat.Prime 13799 := by norm_num

private theorem prime_oneHundredTwentyFourDR_14011 : Nat.Prime 14011 := by norm_num

private theorem prime_oneHundredTwentyFourDR_14657 : Nat.Prime 14657 := by norm_num

private theorem prime_oneHundredTwentyFourDR_15061 : Nat.Prime 15061 := by norm_num

private theorem prime_oneHundredTwentyFourDR_16381 : Nat.Prime 16381 := by norm_num

private theorem prime_oneHundredTwentyFourDR_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentyFourDR_17393 : Nat.Prime 17393 := by norm_num

private theorem prime_oneHundredTwentyFourDR_18541 : Nat.Prime 18541 := by norm_num

private theorem prime_oneHundredTwentyFourDR_18701 : Nat.Prime 18701 := by norm_num

private theorem prime_oneHundredTwentyFourDR_18797 : Nat.Prime 18797 := by norm_num

private theorem prime_oneHundredTwentyFourDR_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredTwentyFourDR_20563 : Nat.Prime 20563 := by norm_num

private theorem prime_oneHundredTwentyFourDR_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentyFourDR_21059 : Nat.Prime 21059 := by norm_num

private theorem prime_oneHundredTwentyFourDR_21341 : Nat.Prime 21341 := by norm_num

private theorem prime_oneHundredTwentyFourDR_21599 : Nat.Prime 21599 := by norm_num

private theorem prime_oneHundredTwentyFourDR_21997 : Nat.Prime 21997 := by norm_num

private theorem prime_oneHundredTwentyFourDR_25939 : Nat.Prime 25939 := by norm_num

private theorem prime_oneHundredTwentyFourDR_26669 : Nat.Prime 26669 := by norm_num

private theorem prime_oneHundredTwentyFourDR_27329 : Nat.Prime 27329 := by norm_num

private theorem prime_oneHundredTwentyFourDR_27791 : Nat.Prime 27791 := by norm_num

private theorem prime_oneHundredTwentyFourDR_29803 : Nat.Prime 29803 := by norm_num

private theorem prime_oneHundredTwentyFourDR_30119 : Nat.Prime 30119 := by norm_num

private theorem prime_oneHundredTwentyFourDR_31253 : Nat.Prime 31253 := by norm_num

private theorem prime_oneHundredTwentyFourDR_32779 : Nat.Prime 32779 := by norm_num

private theorem prime_oneHundredTwentyFourDR_35509 : Nat.Prime 35509 := by norm_num

private theorem prime_oneHundredTwentyFourDR_35797 : Nat.Prime 35797 := by norm_num

private theorem prime_oneHundredTwentyFourDR_42359 : Nat.Prime 42359 := by norm_num

private theorem prime_oneHundredTwentyFourDR_42457 : Nat.Prime 42457 := by norm_num

private theorem prime_oneHundredTwentyFourDR_42703 : Nat.Prime 42703 := by norm_num

private theorem prime_oneHundredTwentyFourDR_42787 : Nat.Prime 42787 := by norm_num

private theorem prime_oneHundredTwentyFourDR_42953 : Nat.Prime 42953 := by norm_num

private theorem prime_oneHundredTwentyFourDR_43391 : Nat.Prime 43391 := by norm_num

private theorem prime_oneHundredTwentyFourDR_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredTwentyFourDR_51151 : Nat.Prime 51151 := by norm_num

private theorem prime_oneHundredTwentyFourDR_52529 : Nat.Prime 52529 := by norm_num

private theorem prime_oneHundredTwentyFourDR_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredTwentyFourDR_54409 : Nat.Prime 54409 := by norm_num

private theorem prime_oneHundredTwentyFourDR_55213 : Nat.Prime 55213 := by norm_num

private theorem prime_oneHundredTwentyFourDR_58193 : Nat.Prime 58193 := by norm_num

private theorem prime_oneHundredTwentyFourDR_59077 : Nat.Prime 59077 := by norm_num

private theorem prime_oneHundredTwentyFourDR_59887 : Nat.Prime 59887 := by norm_num

private theorem prime_oneHundredTwentyFourDR_64067 : Nat.Prime 64067 := by norm_num

private theorem prime_oneHundredTwentyFourDR_64171 : Nat.Prime 64171 := by norm_num

private theorem prime_oneHundredTwentyFourDR_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredTwentyFourDR_73009 : Nat.Prime 73009 := by norm_num

private theorem prime_oneHundredTwentyFourDR_75083 : Nat.Prime 75083 := by norm_num

private theorem prime_oneHundredTwentyFourDR_75169 : Nat.Prime 75169 := by norm_num

private theorem prime_oneHundredTwentyFourDR_75703 : Nat.Prime 75703 := by norm_num

private theorem prime_oneHundredTwentyFourDR_77867 : Nat.Prime 77867 := by norm_num

private theorem prime_oneHundredTwentyFourDR_90187 : Nat.Prime 90187 := by norm_num

private theorem prime_oneHundredTwentyFourDR_91753 : Nat.Prime 91753 := by norm_num

private theorem prime_oneHundredTwentyFourDR_92921 : Nat.Prime 92921 := by norm_num

private theorem prime_oneHundredTwentyFourDR_98407 : Nat.Prime 98407 := by norm_num

private theorem prime_oneHundredTwentyFourDR_106739 : Nat.Prime 106739 := by norm_num

private theorem prime_oneHundredTwentyFourDR_106747 : Nat.Prime 106747 := by norm_num

private theorem prime_oneHundredTwentyFourDR_109721 : Nat.Prime 109721 := by norm_num

private theorem prime_oneHundredTwentyFourDR_123203 : Nat.Prime 123203 := by norm_num

private theorem prime_oneHundredTwentyFourDR_125183 : Nat.Prime 125183 := by norm_num

private theorem prime_oneHundredTwentyFourDR_131023 : Nat.Prime 131023 := by norm_num

private theorem prime_oneHundredTwentyFourDR_155069 : Nat.Prime 155069 := by norm_num

private theorem prime_oneHundredTwentyFourDR_171007 : Nat.Prime 171007 := by norm_num

private theorem prime_oneHundredTwentyFourDR_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentyFourDR_174143 : Nat.Prime 174143 := by norm_num

private theorem prime_oneHundredTwentyFourDR_177223 : Nat.Prime 177223 := by norm_num

private theorem prime_oneHundredTwentyFourDR_181513 : Nat.Prime 181513 := by norm_num

private theorem prime_oneHundredTwentyFourDR_186379 : Nat.Prime 186379 := by norm_num

private theorem prime_oneHundredTwentyFourDR_187193 : Nat.Prime 187193 := by norm_num

private theorem prime_oneHundredTwentyFourDR_188681 : Nat.Prime 188681 := by norm_num

private theorem prime_oneHundredTwentyFourDR_189479 : Nat.Prime 189479 := by norm_num

private theorem prime_oneHundredTwentyFourDR_194867 : Nat.Prime 194867 := by norm_num

private theorem prime_oneHundredTwentyFourDR_196429 : Nat.Prime 196429 := by norm_num

private theorem prime_oneHundredTwentyFourDR_196583 : Nat.Prime 196583 := by norm_num

private theorem prime_oneHundredTwentyFourDR_229267 : Nat.Prime 229267 := by norm_num

private theorem prime_oneHundredTwentyFourDR_234659 : Nat.Prime 234659 := by norm_num

private theorem prime_oneHundredTwentyFourDR_237343 : Nat.Prime 237343 := by norm_num

private theorem prime_oneHundredTwentyFourDR_239857 : Nat.Prime 239857 := by norm_num

private theorem prime_oneHundredTwentyFourDR_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredTwentyFourDR_253871 : Nat.Prime 253871 := by norm_num

private theorem prime_oneHundredTwentyFourDR_267643 : Nat.Prime 267643 := by norm_num

private theorem prime_oneHundredTwentyFourDR_274069 : Nat.Prime 274069 := by norm_num

private theorem prime_oneHundredTwentyFourDR_277531 : Nat.Prime 277531 := by norm_num

private theorem prime_oneHundredTwentyFourDR_296363 : Nat.Prime 296363 := by norm_num

private theorem prime_oneHundredTwentyFourDR_305479 : Nat.Prime 305479 := by norm_num

private theorem prime_oneHundredTwentyFourDR_311533 : Nat.Prime 311533 := by norm_num

private theorem prime_oneHundredTwentyFourDR_318347 : Nat.Prime 318347 := by norm_num

private theorem prime_oneHundredTwentyFourDR_345479 : Nat.Prime 345479 := by norm_num

private theorem prime_oneHundredTwentyFourDR_353501 : Nat.Prime 353501 := by norm_num

private theorem prime_oneHundredTwentyFourDR_360769 : Nat.Prime 360769 := by norm_num

private theorem prime_oneHundredTwentyFourDR_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredTwentyFourDR_372059 : Nat.Prime 372059 := by norm_num

private theorem prime_oneHundredTwentyFourDR_374461 : Nat.Prime 374461 := by norm_num

private theorem prime_oneHundredTwentyFourDR_377557 : Nat.Prime 377557 := by norm_num

private theorem prime_oneHundredTwentyFourDR_395429 : Nat.Prime 395429 := by norm_num

private theorem prime_oneHundredTwentyFourDR_422407 : Nat.Prime 422407 := by norm_num

private theorem prime_oneHundredTwentyFourDR_443873 : Nat.Prime 443873 := by norm_num

private theorem prime_oneHundredTwentyFourDR_457789 : Nat.Prime 457789 := by norm_num

private theorem prime_oneHundredTwentyFourDR_480569 : Nat.Prime 480569 := by norm_num

private theorem prime_oneHundredTwentyFourDR_526193 : Nat.Prime 526193 := by norm_num

private theorem prime_oneHundredTwentyFourDR_560689 : Nat.Prime 560689 := by norm_num

private theorem prime_oneHundredTwentyFourDR_583153 : Nat.Prime 583153 := by norm_num

private theorem prime_oneHundredTwentyFourDR_597899 : Nat.Prime 597899 := by norm_num

private theorem prime_oneHundredTwentyFourDR_607837 : Nat.Prime 607837 := by norm_num

private theorem prime_oneHundredTwentyFourDR_630613 : Nat.Prime 630613 := by norm_num

private theorem prime_oneHundredTwentyFourDR_706193 : Nat.Prime 706193 := by norm_num

private theorem prime_oneHundredTwentyFourDR_754937 : Nat.Prime 754937 := by norm_num

private theorem prime_oneHundredTwentyFourDR_768169 : Nat.Prime 768169 := by norm_num

private theorem prime_oneHundredTwentyFourDR_811763 : Nat.Prime 811763 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1025807 : Nat.Prime 1025807 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1104731 : Nat.Prime 1104731 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1151603 : Nat.Prime 1151603 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1204139 : Nat.Prime 1204139 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1233437 : Nat.Prime 1233437 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1314217 : Nat.Prime 1314217 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1424021 : Nat.Prime 1424021 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1425877 : Nat.Prime 1425877 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1439413 : Nat.Prime 1439413 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1458881 : Nat.Prime 1458881 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1608611 : Nat.Prime 1608611 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1658617 : Nat.Prime 1658617 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1699001 : Nat.Prime 1699001 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1715927 : Nat.Prime 1715927 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1720123 : Nat.Prime 1720123 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1748407 : Nat.Prime 1748407 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1805059 : Nat.Prime 1805059 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1821649 : Nat.Prime 1821649 := by norm_num

private theorem prime_oneHundredTwentyFourDR_1908581 : Nat.Prime 1908581 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2159081 : Nat.Prime 2159081 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2241443 : Nat.Prime 2241443 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2397133 : Nat.Prime 2397133 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2548327 : Nat.Prime 2548327 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2634119 : Nat.Prime 2634119 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2767561 : Nat.Prime 2767561 := by norm_num

private theorem prime_oneHundredTwentyFourDR_2811509 : Nat.Prime 2811509 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3145903 : Nat.Prime 3145903 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3452287 : Nat.Prime 3452287 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3550489 : Nat.Prime 3550489 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3683651 : Nat.Prime 3683651 := by norm_num

private theorem prime_oneHundredTwentyFourDR_3758273 : Nat.Prime 3758273 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4007789 : Nat.Prime 4007789 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4201409 : Nat.Prime 4201409 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4470383 : Nat.Prime 4470383 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4634837 : Nat.Prime 4634837 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4734329 : Nat.Prime 4734329 := by norm_num

private theorem prime_oneHundredTwentyFourDR_4784141 : Nat.Prime 4784141 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5301143 : Nat.Prime 5301143 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5549209 : Nat.Prime 5549209 := by norm_num

private theorem prime_oneHundredTwentyFourDR_5980267 : Nat.Prime 5980267 := by norm_num

private theorem prime_oneHundredTwentyFourDR_6302729 : Nat.Prime 6302729 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7171079 : Nat.Prime 7171079 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7204189 : Nat.Prime 7204189 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7568329 : Nat.Prime 7568329 := by norm_num

private theorem prime_oneHundredTwentyFourDR_7598693 : Nat.Prime 7598693 := by norm_num

private theorem prime_oneHundredTwentyFourDR_8104823 : Nat.Prime 8104823 := by norm_num

private theorem prime_oneHundredTwentyFourDR_8603831 : Nat.Prime 8603831 := by norm_num

private theorem prime_oneHundredTwentyFourDR_9155143 : Nat.Prime 9155143 := by norm_num

private theorem prime_oneHundredTwentyFourDR_9413213 : Nat.Prime 9413213 := by norm_num

private theorem prime_oneHundredTwentyFourDR_9766901 : Nat.Prime 9766901 := by norm_num

private theorem prime_oneHundredTwentyFourDR_10374691 : Nat.Prime 10374691 := by norm_num

private theorem prime_oneHundredTwentyFourDR_10439483 : Nat.Prime 10439483 := by norm_num

private theorem prime_oneHundredTwentyFourDR_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentyFourDR_11462203 : Nat.Prime 11462203 := by norm_num

private theorem prime_oneHundredTwentyFourDR_11704559 : Nat.Prime 11704559 := by norm_num

private theorem prime_oneHundredTwentyFourDR_11747413 : Nat.Prime 11747413 := by norm_num

private theorem prime_oneHundredTwentyFourDR_11747551 : Nat.Prime 11747551 := by norm_num

private theorem prime_oneHundredTwentyFourDR_12595573 : Nat.Prime 12595573 := by norm_num

private theorem prime_oneHundredTwentyFourDR_13809643 : Nat.Prime 13809643 := by norm_num

private theorem prime_oneHundredTwentyFourDR_13909117 : Nat.Prime 13909117 := by norm_num

private theorem prime_oneHundredTwentyFourDR_14114963 : Nat.Prime 14114963 := by norm_num

private theorem prime_oneHundredTwentyFourDR_14161111 : Nat.Prime 14161111 := by norm_num

private theorem prime_oneHundredTwentyFourDR_14171471 : Nat.Prime 14171471 := by norm_num

private theorem prime_oneHundredTwentyFourDR_15629399 : Nat.Prime 15629399 := by norm_num

private theorem prime_oneHundredTwentyFourDR_16161127 : Nat.Prime 16161127 := by norm_num

private theorem prime_oneHundredTwentyFourDR_16164131 : Nat.Prime 16164131 := by norm_num

private theorem prime_oneHundredTwentyFourDR_17239357 : Nat.Prime 17239357 := by norm_num

private theorem prime_oneHundredTwentyFourDR_17517239 : Nat.Prime 17517239 := by norm_num

private theorem prime_oneHundredTwentyFourDR_17751989 : Nat.Prime 17751989 := by norm_num

private theorem prime_oneHundredTwentyFourDR_19743949 : Nat.Prime 19743949 := by norm_num

private theorem prime_oneHundredTwentyFourDR_21203759 : Nat.Prime 21203759 := by norm_num

private theorem prime_oneHundredTwentyFourDR_21715907 : Nat.Prime 21715907 := by norm_num

private theorem prime_oneHundredTwentyFourDR_21834353 : Nat.Prime 21834353 := by norm_num

private theorem prime_oneHundredTwentyFourDR_23130377 : Nat.Prime 23130377 := by norm_num

private theorem prime_oneHundredTwentyFourDR_23215867 : Nat.Prime 23215867 := by norm_num

private theorem prime_oneHundredTwentyFourDR_24177523 : Nat.Prime 24177523 := by norm_num

private theorem prime_oneHundredTwentyFourDR_24220619 : Nat.Prime 24220619 := by norm_num

private theorem prime_oneHundredTwentyFourDR_27177767 : Nat.Prime 27177767 := by norm_num

private theorem prime_oneHundredTwentyFourDR_28679857 : Nat.Prime 28679857 := by norm_num

private theorem prime_oneHundredTwentyFourDR_29655581 : Nat.Prime 29655581 := by norm_num

private theorem prime_oneHundredTwentyFourDR_31784069 : Nat.Prime 31784069 := by
  apply lucas_primality 31784069 (2 : ZMod 31784069)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (345479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (345479, 1)] : List FactorBlock).map factorBlockValue).prod) = 31784069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_345479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31784069) ^ 15892034 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 31784069) ^ 1381916 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 31784069) ^ 92 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_32683141 : Nat.Prime 32683141 := by
  apply lucas_primality 32683141 (18 : ZMod 32683141)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (25939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (25939, 1)] : List FactorBlock).map factorBlockValue).prod) = 32683141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_25939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 32683141) ^ 16341570 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (18 : ZMod 32683141) ^ 10894380 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (18 : ZMod 32683141) ^ 6536628 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (18 : ZMod 32683141) ^ 4669020 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (18 : ZMod 32683141) ^ 1260 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_36877667 : Nat.Prime 36877667 := by
  apply lucas_primality 36877667 (2 : ZMod 36877667)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2634119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2634119, 1)] : List FactorBlock).map factorBlockValue).prod) = 36877667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_2634119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36877667) ^ 18438833 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 36877667) ^ 5268238 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 36877667) ^ 14 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_38270863 : Nat.Prime 38270863 := by
  apply lucas_primality 38270863 (3 : ZMod 38270863)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (43391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (43391, 1)] : List FactorBlock).map factorBlockValue).prod) = 38270863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_43391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38270863) ^ 19135431 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38270863) ^ 12756954 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38270863) ^ 5467266 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38270863) ^ 882 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_38273129 : Nat.Prime 38273129 := by
  apply lucas_primality 38273129 (3 : ZMod 38273129)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4784141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4784141, 1)] : List FactorBlock).map factorBlockValue).prod) = 38273129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_4784141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 38273129) ^ 19136564 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38273129) ^ 8 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_39548843 : Nat.Prime 39548843 := by
  apply lucas_primality 39548843 (2 : ZMod 39548843)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (191, 1), (5449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (191, 1), (5449, 1)] : List FactorBlock).map factorBlockValue).prod) = 39548843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_191
      · exact prime_oneHundredTwentyFourDR_5449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39548843) ^ 19774421 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 39548843) ^ 2081518 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 39548843) ^ 207062 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 39548843) ^ 7258 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_40440481 : Nat.Prime 40440481 := by
  apply lucas_primality 40440481 (17 : ZMod 40440481)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (173, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (173, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) = 40440481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_173
      · exact prime_oneHundredTwentyFourDR_487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 40440481) ^ 20220240 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 40440481) ^ 13480160 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 40440481) ^ 8088096 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 40440481) ^ 233760 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 40440481) ^ 83040 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_47229857 : Nat.Prime 47229857 := by
  apply lucas_primality 47229857 (3 : ZMod 47229857)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (64171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (64171, 1)] : List FactorBlock).map factorBlockValue).prod) = 47229857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_64171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47229857) ^ 23614928 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 47229857) ^ 2053472 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 47229857) ^ 736 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_48906269 : Nat.Prime 48906269 := by
  apply lucas_primality 48906269 (2 : ZMod 48906269)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (32779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (32779, 1)] : List FactorBlock).map factorBlockValue).prod) = 48906269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_373
      · exact prime_oneHundredTwentyFourDR_32779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 48906269) ^ 24453134 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 48906269) ^ 131116 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 48906269) ^ 1492 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_51603691 : Nat.Prime 51603691 := by
  apply lucas_primality 51603691 (2 : ZMod 51603691)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1720123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1720123, 1)] : List FactorBlock).map factorBlockValue).prod) = 51603691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_1720123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51603691) ^ 25801845 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 51603691) ^ 17201230 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 51603691) ^ 10320738 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 51603691) ^ 30 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_52870897 : Nat.Prime 52870897 := by
  apply lucas_primality 52870897 (11 : ZMod 52870897)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (61, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (61, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 52870897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_61
      · exact prime_oneHundredTwentyFourDR_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 52870897) ^ 26435448 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 52870897) ^ 17623632 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 52870897) ^ 4066992 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 52870897) ^ 866736 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 52870897) ^ 114192 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_57693803 : Nat.Prime 57693803 := by
  apply lucas_primality 57693803 (2 : ZMod 57693803)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (229, 1), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (229, 1), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) = 57693803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_103
      · exact prime_oneHundredTwentyFourDR_229
      · exact prime_oneHundredTwentyFourDR_1223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57693803) ^ 28846901 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57693803) ^ 560134 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57693803) ^ 251938 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57693803) ^ 47174 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_1811
      · exact prime_oneHundredTwentyFourDR_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_60732599 : Nat.Prime 60732599 := by
  apply lucas_primality 60732599 (7 : ZMod 60732599)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (706193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (706193, 1)] : List FactorBlock).map factorBlockValue).prod) = 60732599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_43
      · exact prime_oneHundredTwentyFourDR_706193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 60732599) ^ 30366299 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 60732599) ^ 1412386 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 60732599) ^ 86 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_64450391 : Nat.Prime 64450391 := by
  apply lucas_primality 64450391 (13 : ZMod 64450391)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2459, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2459, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) = 64450391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_2459
      · exact prime_oneHundredTwentyFourDR_2621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 64450391) ^ 32225195 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 64450391) ^ 12890078 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 64450391) ^ 26210 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 64450391) ^ 24590 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_66283709 : Nat.Prime 66283709 := by
  apply lucas_primality 66283709 (2 : ZMod 66283709)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (73, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (73, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod) = 66283709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_53
      · exact prime_oneHundredTwentyFourDR_73
      · exact prime_oneHundredTwentyFourDR_4283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66283709) ^ 33141854 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 66283709) ^ 1250636 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 66283709) ^ 907996 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 66283709) ^ 15476 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_68957429 : Nat.Prime 68957429 := by
  apply lucas_primality 68957429 (2 : ZMod 68957429)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17239357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17239357, 1)] : List FactorBlock).map factorBlockValue).prod) = 68957429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_17239357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 68957429) ^ 34478714 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 68957429) ^ 4 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_71445277 : Nat.Prime 71445277 := by
  apply lucas_primality 71445277 (2 : ZMod 71445277)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (509, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (509, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) = 71445277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_509
      · exact prime_oneHundredTwentyFourDR_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71445277) ^ 35722638 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 71445277) ^ 23815092 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 71445277) ^ 10206468 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 71445277) ^ 140364 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 71445277) ^ 128268 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_75683291 : Nat.Prime 75683291 := by
  apply lucas_primality 75683291 (2 : ZMod 75683291)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7568329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7568329, 1)] : List FactorBlock).map factorBlockValue).prod) = 75683291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_7568329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75683291) ^ 37841645 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 75683291) ^ 15136658 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 75683291) ^ 10 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_77973617 : Nat.Prime 77973617 := by
  apply lucas_primality 77973617 (5 : ZMod 77973617)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (61, 1), (101, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (61, 1), (101, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 77973617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_61
      · exact prime_oneHundredTwentyFourDR_101
      · exact prime_oneHundredTwentyFourDR_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77973617) ^ 38986808 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 77973617) ^ 11139088 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 77973617) ^ 1278256 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 77973617) ^ 772016 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 77973617) ^ 690032 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_79810561 : Nat.Prime 79810561 := by
  apply lucas_primality 79810561 (7 : ZMod 79810561)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (3, 2), (5, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (3, 2), (5, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) = 79810561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 79810561) ^ 39905280 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 79810561) ^ 26603520 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 79810561) ^ 15962112 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 79810561) ^ 184320 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_83517169 : Nat.Prime 83517169 := by
  apply lucas_primality 83517169 (11 : ZMod 83517169)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (35509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (35509, 1)] : List FactorBlock).map factorBlockValue).prod) = 83517169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_35509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 83517169) ^ 41758584 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 83517169) ^ 27839056 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 83517169) ^ 11931024 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 83517169) ^ 2352 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_88238207 : Nat.Prime 88238207 := by
  apply lucas_primality 88238207 (7 : ZMod 88238207)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6302729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6302729, 1)] : List FactorBlock).map factorBlockValue).prod) = 88238207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_6302729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 88238207) ^ 44119103 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 88238207) ^ 12605458 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 88238207) ^ 14 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_94243111 : Nat.Prime 94243111 := by
  apply lucas_primality 94243111 (7 : ZMod 94243111)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (167, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (167, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) = 94243111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_167
      · exact prime_oneHundredTwentyFourDR_1447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 94243111) ^ 47121555 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 94243111) ^ 31414370 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 94243111) ^ 18848622 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 94243111) ^ 7249470 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 94243111) ^ 564330 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 94243111) ^ 65130 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_120243971 : Nat.Prime 120243971 := by
  apply lucas_primality 120243971 (7 : ZMod 120243971)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (19, 1), (8219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (19, 1), (8219, 1)] : List FactorBlock).map factorBlockValue).prod) = 120243971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_8219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 120243971) ^ 60121985 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 120243971) ^ 24048794 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 120243971) ^ 17177710 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 120243971) ^ 10931270 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 120243971) ^ 6328630 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 120243971) ^ 14630 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_121891867 : Nat.Prime 121891867 := by
  apply lucas_primality 121891867 (3 : ZMod 121891867)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (186379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (186379, 1)] : List FactorBlock).map factorBlockValue).prod) = 121891867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_109
      · exact prime_oneHundredTwentyFourDR_186379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 121891867) ^ 60945933 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 121891867) ^ 40630622 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 121891867) ^ 1118274 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 121891867) ^ 654 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_139986397 : Nat.Prime 139986397 := by
  apply lucas_primality 139986397 (5 : ZMod 139986397)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (353501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (353501, 1)] : List FactorBlock).map factorBlockValue).prod) = 139986397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_353501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 139986397) ^ 69993198 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 139986397) ^ 46662132 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 139986397) ^ 12726036 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 139986397) ^ 396 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_152335717 : Nat.Prime 152335717 := by
  apply lucas_primality 152335717 (2 : ZMod 152335717)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (23, 1), (42457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (23, 1), (42457, 1)] : List FactorBlock).map factorBlockValue).prod) = 152335717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_42457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 152335717) ^ 76167858 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 152335717) ^ 50778572 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 152335717) ^ 11718132 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 152335717) ^ 6623292 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 152335717) ^ 3588 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_155791897 : Nat.Prime 155791897 := by
  apply lucas_primality 155791897 (5 : ZMod 155791897)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (347, 1), (1439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (347, 1), (1439, 1)] : List FactorBlock).map factorBlockValue).prod) = 155791897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_347
      · exact prime_oneHundredTwentyFourDR_1439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155791897) ^ 77895948 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 155791897) ^ 51930632 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 155791897) ^ 11983992 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 155791897) ^ 448968 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 155791897) ^ 108264 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_199488901 : Nat.Prime 199488901 := by
  apply lucas_primality 199488901 (2 : ZMod 199488901)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (51151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (51151, 1)] : List FactorBlock).map factorBlockValue).prod) = 199488901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_51151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 199488901) ^ 99744450 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 199488901) ^ 66496300 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 199488901) ^ 39897780 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 199488901) ^ 15345300 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 199488901) ^ 3900 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_220593953 : Nat.Prime 220593953 := by
  apply lucas_primality 220593953 (3 : ZMod 220593953)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (29, 1), (12511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (29, 1), (12511, 1)] : List FactorBlock).map factorBlockValue).prod) = 220593953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_29
      · exact prime_oneHundredTwentyFourDR_12511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 220593953) ^ 110296976 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 220593953) ^ 11610208 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 220593953) ^ 7606688 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 220593953) ^ 17632 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_231958477 : Nat.Prime 231958477 := by
  apply lucas_primality 231958477 (5 : ZMod 231958477)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (37, 1), (174143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (37, 1), (174143, 1)] : List FactorBlock).map factorBlockValue).prod) = 231958477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_174143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 231958477) ^ 115979238 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 231958477) ^ 77319492 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 231958477) ^ 6269148 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 231958477) ^ 1332 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_236850169 : Nat.Prime 236850169 := by
  apply lucas_primality 236850169 (7 : ZMod 236850169)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (318347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (318347, 1)] : List FactorBlock).map factorBlockValue).prod) = 236850169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_318347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 236850169) ^ 118425084 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 236850169) ^ 78950056 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 236850169) ^ 7640328 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 236850169) ^ 744 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_324964763 : Nat.Prime 324964763 := by
  apply lucas_primality 324964763 (2 : ZMod 324964763)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (659, 1), (3121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (659, 1), (3121, 1)] : List FactorBlock).map factorBlockValue).prod) = 324964763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_79
      · exact prime_oneHundredTwentyFourDR_659
      · exact prime_oneHundredTwentyFourDR_3121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 324964763) ^ 162482381 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 324964763) ^ 4113478 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 324964763) ^ 493118 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 324964763) ^ 104122 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_337822627 : Nat.Prime 337822627 := by
  apply lucas_primality 337822627 (3 : ZMod 337822627)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (457, 1), (123203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (457, 1), (123203, 1)] : List FactorBlock).map factorBlockValue).prod) = 337822627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_457
      · exact prime_oneHundredTwentyFourDR_123203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 337822627) ^ 168911313 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 337822627) ^ 112607542 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 337822627) ^ 739218 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 337822627) ^ 2742 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_349875439 : Nat.Prime 349875439 := by
  apply lucas_primality 349875439 (3 : ZMod 349875439)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5301143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5301143, 1)] : List FactorBlock).map factorBlockValue).prod) = 349875439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_5301143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 349875439) ^ 174937719 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 349875439) ^ 116625146 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 349875439) ^ 31806858 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 349875439) ^ 66 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_358001093 : Nat.Prime 358001093 := by
  apply lucas_primality 358001093 (2 : ZMod 358001093)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1621, 1), (55213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1621, 1), (55213, 1)] : List FactorBlock).map factorBlockValue).prod) = 358001093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_1621
      · exact prime_oneHundredTwentyFourDR_55213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 358001093) ^ 179000546 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 358001093) ^ 220852 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 358001093) ^ 6484 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_381716201 : Nat.Prime 381716201 := by
  apply lucas_primality 381716201 (3 : ZMod 381716201)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (1908581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (1908581, 1)] : List FactorBlock).map factorBlockValue).prod) = 381716201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_1908581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 381716201) ^ 190858100 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 381716201) ^ 76343240 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 381716201) ^ 200 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_433055573 : Nat.Prime 433055573 := by
  apply lucas_primality 433055573 (2 : ZMod 433055573)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (239, 1), (6761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (239, 1), (6761, 1)] : List FactorBlock).map factorBlockValue).prod) = 433055573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_67
      · exact prime_oneHundredTwentyFourDR_239
      · exact prime_oneHundredTwentyFourDR_6761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 433055573) ^ 216527786 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 433055573) ^ 6463516 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 433055573) ^ 1811948 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 433055573) ^ 64052 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_443517293 : Nat.Prime 443517293 := by
  apply lucas_primality 443517293 (2 : ZMod 443517293)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (569, 1), (194867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (569, 1), (194867, 1)] : List FactorBlock).map factorBlockValue).prod) = 443517293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_569
      · exact prime_oneHundredTwentyFourDR_194867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 443517293) ^ 221758646 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 443517293) ^ 779468 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 443517293) ^ 2276 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_452748809 : Nat.Prime 452748809 := by
  apply lucas_primality 452748809 (3 : ZMod 452748809)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1879, 1), (30119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1879, 1), (30119, 1)] : List FactorBlock).map factorBlockValue).prod) = 452748809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_1879
      · exact prime_oneHundredTwentyFourDR_30119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 452748809) ^ 226374404 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 452748809) ^ 240952 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 452748809) ^ 15032 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_486985013 : Nat.Prime 486985013 := by
  apply lucas_primality 486985013 (2 : ZMod 486985013)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2851, 1), (42703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2851, 1), (42703, 1)] : List FactorBlock).map factorBlockValue).prod) = 486985013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_2851
      · exact prime_oneHundredTwentyFourDR_42703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 486985013) ^ 243492506 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 486985013) ^ 170812 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 486985013) ^ 11404 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_557180809 : Nat.Prime 557180809 := by
  apply lucas_primality 557180809 (14 : ZMod 557180809)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23215867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23215867, 1)] : List FactorBlock).map factorBlockValue).prod) = 557180809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_23215867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 557180809) ^ 278590404 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (14 : ZMod 557180809) ^ 185726936 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (14 : ZMod 557180809) ^ 24 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_588296539 : Nat.Prime 588296539 := by
  apply lucas_primality 588296539 (2 : ZMod 588296539)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (32683141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (32683141, 1)] : List FactorBlock).map factorBlockValue).prod) = 588296539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_32683141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 588296539) ^ 294148269 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 588296539) ^ 196098846 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 588296539) ^ 18 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_618853369 : Nat.Prime 618853369 := by
  apply lucas_primality 618853369 (17 : ZMod 618853369)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (3683651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (3683651, 1)] : List FactorBlock).map factorBlockValue).prod) = 618853369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_3683651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 618853369) ^ 309426684 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 618853369) ^ 206284456 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 618853369) ^ 88407624 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 618853369) ^ 168 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_669676067 : Nat.Prime 669676067 := by
  apply lucas_primality 669676067 (2 : ZMod 669676067)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (1013, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (1013, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) = 669676067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_43
      · exact prime_oneHundredTwentyFourDR_1013
      · exact prime_oneHundredTwentyFourDR_7687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 669676067) ^ 334838033 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 669676067) ^ 15573862 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 669676067) ^ 661082 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 669676067) ^ 87118 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_680335493 : Nat.Prime 680335493 := by
  apply lucas_primality 680335493 (2 : ZMod 680335493)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (491, 1), (15061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (491, 1), (15061, 1)] : List FactorBlock).map factorBlockValue).prod) = 680335493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_491
      · exact prime_oneHundredTwentyFourDR_15061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 680335493) ^ 340167746 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 680335493) ^ 29579804 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 680335493) ^ 1385612 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 680335493) ^ 45172 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_686808323 : Nat.Prime 686808323 := by
  apply lucas_primality 686808323 (2 : ZMod 686808323)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (1021, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (1021, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) = 686808323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_179
      · exact prime_oneHundredTwentyFourDR_1021
      · exact prime_oneHundredTwentyFourDR_1879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 686808323) ^ 343404161 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 686808323) ^ 3836918 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 686808323) ^ 672682 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 686808323) ^ 365518 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_17203
      · exact prime_oneHundredTwentyFourDR_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_716002187 : Nat.Prime 716002187 := by
  apply lucas_primality 716002187 (2 : ZMod 716002187)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (358001093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (358001093, 1)] : List FactorBlock).map factorBlockValue).prod) = 716002187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_358001093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 716002187) ^ 358001093 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 716002187) ^ 2 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_927150877 : Nat.Prime 927150877 := by
  apply lucas_primality 927150877 (2 : ZMod 927150877)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (449, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (449, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 927150877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_41
      · exact prime_oneHundredTwentyFourDR_449
      · exact prime_oneHundredTwentyFourDR_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 927150877) ^ 463575438 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 927150877) ^ 309050292 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 927150877) ^ 22613436 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 927150877) ^ 2064924 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 927150877) ^ 662724 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_953305159 : Nat.Prime 953305159 := by
  apply lucas_primality 953305159 (41 : ZMod 953305159)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (107, 1), (6719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (107, 1), (6719, 1)] : List FactorBlock).map factorBlockValue).prod) = 953305159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_107
      · exact prime_oneHundredTwentyFourDR_6719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 953305159) ^ 476652579 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (41 : ZMod 953305159) ^ 317768386 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (41 : ZMod 953305159) ^ 73331166 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (41 : ZMod 953305159) ^ 56076774 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (41 : ZMod 953305159) ^ 8909394 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (41 : ZMod 953305159) ^ 141882 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_966324071 : Nat.Prime 966324071 := by
  apply lucas_primality 966324071 (11 : ZMod 966324071)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (4201409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (4201409, 1)] : List FactorBlock).map factorBlockValue).prod) = 966324071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_4201409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 966324071) ^ 483162035 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 966324071) ^ 193264814 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 966324071) ^ 42014090 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 966324071) ^ 230 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1067600917 : Nat.Prime 1067600917 := by
  apply lucas_primality 1067600917 (2 : ZMod 1067600917)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29655581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29655581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067600917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_29655581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1067600917) ^ 533800458 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067600917) ^ 355866972 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067600917) ^ 36 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1114172737 : Nat.Prime 1114172737 := by
  apply lucas_primality 1114172737 (7 : ZMod 1114172737)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (31, 1), (187193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (31, 1), (187193, 1)] : List FactorBlock).map factorBlockValue).prod) = 1114172737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_187193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1114172737) ^ 557086368 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1114172737) ^ 371390912 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1114172737) ^ 35941056 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1114172737) ^ 5952 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1193106763 : Nat.Prime 1193106763 := by
  apply lucas_primality 1193106763 (2 : ZMod 1193106763)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (66283709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (66283709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1193106763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_66283709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1193106763) ^ 596553381 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1193106763) ^ 397702254 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1193106763) ^ 18 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1243119329 : Nat.Prime 1243119329 := by
  apply lucas_primality 1243119329 (3 : ZMod 1243119329)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (113, 1), (31253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (113, 1), (31253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1243119329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_113
      · exact prime_oneHundredTwentyFourDR_31253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1243119329) ^ 621559664 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1243119329) ^ 113010848 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1243119329) ^ 11001056 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1243119329) ^ 39776 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1399501757 : Nat.Prime 1399501757 := by
  apply lucas_primality 1399501757 (2 : ZMod 1399501757)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (349875439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (349875439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1399501757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_349875439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1399501757) ^ 699750878 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399501757) ^ 4 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1541895151 : Nat.Prime 1541895151 := by
  apply lucas_primality 1541895151 (6 : ZMod 1541895151)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (83, 1), (271, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (83, 1), (271, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1541895151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_83
      · exact prime_oneHundredTwentyFourDR_271
      · exact prime_oneHundredTwentyFourDR_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1541895151) ^ 770947575 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1541895151) ^ 513965050 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1541895151) ^ 308379030 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1541895151) ^ 18577050 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1541895151) ^ 5689650 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1541895151) ^ 3373950 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1724456831 : Nat.Prime 1724456831 := by
  apply lucas_primality 1724456831 (11 : ZMod 1724456831)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (1249, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (1249, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) = 1724456831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_101
      · exact prime_oneHundredTwentyFourDR_1249
      · exact prime_oneHundredTwentyFourDR_1367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1724456831) ^ 862228415 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1724456831) ^ 344891366 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1724456831) ^ 17073830 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1724456831) ^ 1380670 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1724456831) ^ 1261490 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2016677753 : Nat.Prime 2016677753 := by
  apply lucas_primality 2016677753 (3 : ZMod 2016677753)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (3550489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (3550489, 1)] : List FactorBlock).map factorBlockValue).prod) = 2016677753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_71
      · exact prime_oneHundredTwentyFourDR_3550489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2016677753) ^ 1008338876 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016677753) ^ 28403912 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016677753) ^ 568 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2024596309 : Nat.Prime 2024596309 := by
  apply lucas_primality 2024596309 (2 : ZMod 2024596309)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (73, 1), (101, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (73, 1), (101, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 2024596309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_73
      · exact prime_oneHundredTwentyFourDR_101
      · exact prime_oneHundredTwentyFourDR_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2024596309) ^ 1012298154 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2024596309) ^ 674865436 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2024596309) ^ 289228044 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2024596309) ^ 27734196 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2024596309) ^ 20045508 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2024596309) ^ 4335324 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2291598263 : Nat.Prime 2291598263 := by
  apply lucas_primality 2291598263 (5 : ZMod 2291598263)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21059, 1), (54409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21059, 1), (54409, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291598263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_21059
      · exact prime_oneHundredTwentyFourDR_54409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2291598263) ^ 1145799131 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2291598263) ^ 108818 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2291598263) ^ 42118 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2338480733 : Nat.Prime 2338480733 := by
  apply lucas_primality 2338480733 (5 : ZMod 2338480733)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (83517169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (83517169, 1)] : List FactorBlock).map factorBlockValue).prod) = 2338480733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_83517169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2338480733) ^ 1169240366 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2338480733) ^ 334068676 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2338480733) ^ 28 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_47
      · exact prime_oneHundredTwentyFourDR_71
      · exact prime_oneHundredTwentyFourDR_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2553160849 : Nat.Prime 2553160849 := by
  apply lucas_primality 2553160849 (11 : ZMod 2553160849)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (7598693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (7598693, 1)] : List FactorBlock).map factorBlockValue).prod) = 2553160849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_7598693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2553160849) ^ 1276580424 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 2553160849) ^ 851053616 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 2553160849) ^ 364737264 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 2553160849) ^ 336 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_3069944617 : Nat.Prime 3069944617 := by
  apply lucas_primality 3069944617 (5 : ZMod 3069944617)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6899, 1), (18541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6899, 1), (18541, 1)] : List FactorBlock).map factorBlockValue).prod) = 3069944617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_6899
      · exact prime_oneHundredTwentyFourDR_18541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3069944617) ^ 1534972308 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 3069944617) ^ 1023314872 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 3069944617) ^ 444984 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 3069944617) ^ 165576 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_3213453469 : Nat.Prime 3213453469 := by
  apply lucas_primality 3213453469 (2 : ZMod 3213453469)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (71, 1), (239, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (71, 1), (239, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) = 3213453469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_43
      · exact prime_oneHundredTwentyFourDR_71
      · exact prime_oneHundredTwentyFourDR_239
      · exact prime_oneHundredTwentyFourDR_367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3213453469) ^ 1606726734 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3213453469) ^ 1071151156 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3213453469) ^ 74731476 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3213453469) ^ 45259908 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3213453469) ^ 13445412 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3213453469) ^ 8756004 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_3230852969 : Nat.Prime 3230852969 := by
  apply lucas_primality 3230852969 (6 : ZMod 3230852969)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (57693803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (57693803, 1)] : List FactorBlock).map factorBlockValue).prod) = 3230852969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_57693803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 3230852969) ^ 1615426484 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 3230852969) ^ 461550424 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 3230852969) ^ 56 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_3345398857 : Nat.Prime 3345398857 := by
  apply lucas_primality 3345398857 (7 : ZMod 3345398857)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (19, 1), (97, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (19, 1), (97, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 3345398857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_97
      · exact prime_oneHundredTwentyFourDR_1483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3345398857) ^ 1672699428 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3345398857) ^ 1115132952 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3345398857) ^ 196788168 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3345398857) ^ 176073624 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3345398857) ^ 34488648 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3345398857) ^ 2255832 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_3641820779 : Nat.Prime 3641820779 := by
  apply lucas_primality 3641820779 (2 : ZMod 3641820779)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (27177767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (27177767, 1)] : List FactorBlock).map factorBlockValue).prod) = 3641820779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_67
      · exact prime_oneHundredTwentyFourDR_27177767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3641820779) ^ 1820910389 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641820779) ^ 54355534 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641820779) ^ 134 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_4516788161 : Nat.Prime 4516788161 := by
  apply lucas_primality 4516788161 (3 : ZMod 4516788161)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (14114963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (14114963, 1)] : List FactorBlock).map factorBlockValue).prod) = 4516788161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_14114963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4516788161) ^ 2258394080 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4516788161) ^ 903357632 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4516788161) ^ 320 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_5291148787 : Nat.Prime 5291148787 := by
  apply lucas_primality 5291148787 (3 : ZMod 5291148787)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (1301, 1), (8803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (1301, 1), (8803, 1)] : List FactorBlock).map factorBlockValue).prod) = 5291148787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_1301
      · exact prime_oneHundredTwentyFourDR_8803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5291148787) ^ 2645574393 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5291148787) ^ 1763716262 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5291148787) ^ 755878398 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5291148787) ^ 481013526 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5291148787) ^ 4066986 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5291148787) ^ 601062 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_5656299799 : Nat.Prime 5656299799 := by
  apply lucas_primality 5656299799 (3 : ZMod 5656299799)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (919, 1), (1025807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (919, 1), (1025807, 1)] : List FactorBlock).map factorBlockValue).prod) = 5656299799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_919
      · exact prime_oneHundredTwentyFourDR_1025807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5656299799) ^ 2828149899 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5656299799) ^ 1885433266 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5656299799) ^ 6154842 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5656299799) ^ 5514 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_6188533691 : Nat.Prime 6188533691 := by
  apply lucas_primality 6188533691 (2 : ZMod 6188533691)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (618853369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (618853369, 1)] : List FactorBlock).map factorBlockValue).prod) = 6188533691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_618853369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6188533691) ^ 3094266845 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6188533691) ^ 1237706738 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6188533691) ^ 10 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_7471442437 : Nat.Prime 7471442437 := by
  apply lucas_primality 7471442437 (2 : ZMod 7471442437)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (11747551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (11747551, 1)] : List FactorBlock).map factorBlockValue).prod) = 7471442437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_53
      · exact prime_oneHundredTwentyFourDR_11747551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7471442437) ^ 3735721218 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7471442437) ^ 2490480812 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7471442437) ^ 140970612 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7471442437) ^ 636 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_8006825591 : Nat.Prime 8006825591 := by
  apply lucas_primality 8006825591 (7 : ZMod 8006825591)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4073, 1), (196583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4073, 1), (196583, 1)] : List FactorBlock).map factorBlockValue).prod) = 8006825591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_4073
      · exact prime_oneHundredTwentyFourDR_196583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8006825591) ^ 4003412795 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 8006825591) ^ 1601365118 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 8006825591) ^ 1965830 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 8006825591) ^ 40730 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_8184194567 : Nat.Prime 8184194567 := by
  apply lucas_primality 8184194567 (5 : ZMod 8184194567)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 2), (811763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 2), (811763, 1)] : List FactorBlock).map factorBlockValue).prod) = 8184194567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_71
      · exact prime_oneHundredTwentyFourDR_811763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8184194567) ^ 4092097283 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8184194567) ^ 115270346 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8184194567) ^ 10082 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_8556762187 : Nat.Prime 8556762187 := by
  apply lucas_primality 8556762187 (2 : ZMod 8556762187)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (251, 1), (90187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (251, 1), (90187, 1)] : List FactorBlock).map factorBlockValue).prod) = 8556762187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_251
      · exact prime_oneHundredTwentyFourDR_90187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8556762187) ^ 4278381093 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556762187) ^ 2852254062 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556762187) ^ 1222394598 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556762187) ^ 34090686 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556762187) ^ 94878 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_8719229287 : Nat.Prime 8719229287 := by
  apply lucas_primality 8719229287 (3 : ZMod 8719229287)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (5980267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (5980267, 1)] : List FactorBlock).map factorBlockValue).prod) = 8719229287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5980267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8719229287) ^ 4359614643 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719229287) ^ 2906409762 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719229287) ^ 1458 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_9556376147 : Nat.Prime 9556376147 := by
  apply lucas_primality 9556376147 (2 : ZMod 9556376147)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (6571, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (6571, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) = 9556376147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_83
      · exact prime_oneHundredTwentyFourDR_6571
      · exact prime_oneHundredTwentyFourDR_8761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9556376147) ^ 4778188073 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9556376147) ^ 115137062 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9556376147) ^ 1454326 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9556376147) ^ 1090786 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_9644257477 : Nat.Prime 9644257477 := by
  apply lucas_primality 9644257477 (2 : ZMod 9644257477)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (38270863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (38270863, 1)] : List FactorBlock).map factorBlockValue).prod) = 9644257477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_38270863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9644257477) ^ 4822128738 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9644257477) ^ 3214752492 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9644257477) ^ 1377751068 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9644257477) ^ 252 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_10128617189 : Nat.Prime 10128617189 := by
  apply lucas_primality 10128617189 (2 : ZMod 10128617189)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (269, 1), (9413213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (269, 1), (9413213, 1)] : List FactorBlock).map factorBlockValue).prod) = 10128617189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_269
      · exact prime_oneHundredTwentyFourDR_9413213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10128617189) ^ 5064308594 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10128617189) ^ 37652852 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 10128617189) ^ 1076 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_10309963273 : Nat.Prime 10309963273 := by
  apply lucas_primality 10309963273 (5 : ZMod 10309963273)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (37, 1), (1658617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (37, 1), (1658617, 1)] : List FactorBlock).map factorBlockValue).prod) = 10309963273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_1658617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10309963273) ^ 5154981636 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10309963273) ^ 3436654424 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10309963273) ^ 1472851896 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10309963273) ^ 278647656 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 10309963273) ^ 6216 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_11840184173 : Nat.Prime 11840184173 := by
  apply lucas_primality 11840184173 (2 : ZMod 11840184173)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (155791897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (155791897, 1)] : List FactorBlock).map factorBlockValue).prod) = 11840184173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_155791897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11840184173) ^ 5920092086 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11840184173) ^ 623167588 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11840184173) ^ 76 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_12132144301 : Nat.Prime 12132144301 := by
  apply lucas_primality 12132144301 (2 : ZMod 12132144301)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (40440481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (40440481, 1)] : List FactorBlock).map factorBlockValue).prod) = 12132144301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_40440481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12132144301) ^ 6066072150 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12132144301) ^ 4044048100 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12132144301) ^ 2426428860 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 12132144301) ^ 300 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_13272969907 : Nat.Prime 13272969907 := by
  apply lucas_primality 13272969907 (3 : ZMod 13272969907)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (11704559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (11704559, 1)] : List FactorBlock).map factorBlockValue).prod) = 13272969907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_11704559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13272969907) ^ 6636484953 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13272969907) ^ 4424323302 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13272969907) ^ 1896138558 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 13272969907) ^ 1134 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_14797189313 : Nat.Prime 14797189313 := by
  apply lucas_primality 14797189313 (3 : ZMod 14797189313)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (227, 1), (277, 1), (3677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (227, 1), (277, 1), (3677, 1)] : List FactorBlock).map factorBlockValue).prod) = 14797189313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_227
      · exact prime_oneHundredTwentyFourDR_277
      · exact prime_oneHundredTwentyFourDR_3677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14797189313) ^ 7398594656 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 14797189313) ^ 65185856 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 14797189313) ^ 53419456 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 14797189313) ^ 4024256 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_14827918429 : Nat.Prime 14827918429 := by
  apply lucas_primality 14827918429 (2 : ZMod 14827918429)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (29, 1), (4734329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (29, 1), (4734329, 1)] : List FactorBlock).map factorBlockValue).prod) = 14827918429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_29
      · exact prime_oneHundredTwentyFourDR_4734329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14827918429) ^ 7413959214 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 14827918429) ^ 4942639476 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 14827918429) ^ 511307532 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 14827918429) ^ 3132 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_16093721209 : Nat.Prime 16093721209 := by
  apply lucas_primality 16093721209 (21 : ZMod 16093721209)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (607, 1), (1104731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (607, 1), (1104731, 1)] : List FactorBlock).map factorBlockValue).prod) = 16093721209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_607
      · exact prime_oneHundredTwentyFourDR_1104731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 16093721209) ^ 8046860604 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (21 : ZMod 16093721209) ^ 5364573736 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (21 : ZMod 16093721209) ^ 26513544 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (21 : ZMod 16093721209) ^ 14568 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_18940400231 : Nat.Prime 18940400231 := by
  apply lucas_primality 18940400231 (11 : ZMod 18940400231)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (19, 1), (211, 1), (27791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (19, 1), (211, 1), (27791, 1)] : List FactorBlock).map factorBlockValue).prod) = 18940400231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_211
      · exact prime_oneHundredTwentyFourDR_27791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 18940400231) ^ 9470200115 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 18940400231) ^ 3788080046 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 18940400231) ^ 1114141190 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 18940400231) ^ 996863170 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 18940400231) ^ 89764930 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 18940400231) ^ 681530 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_20604249691 : Nat.Prime 20604249691 := by
  apply lucas_primality 20604249691 (2 : ZMod 20604249691)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (686808323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (686808323, 1)] : List FactorBlock).map factorBlockValue).prod) = 20604249691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_686808323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20604249691) ^ 10302124845 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 20604249691) ^ 6868083230 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 20604249691) ^ 4120849938 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 20604249691) ^ 30 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_22500583207 : Nat.Prime 22500583207 := by
  apply lucas_primality 22500583207 (3 : ZMod 22500583207)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (220593953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (220593953, 1)] : List FactorBlock).map factorBlockValue).prod) = 22500583207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_220593953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22500583207) ^ 11250291603 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 22500583207) ^ 7500194402 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 22500583207) ^ 1323563718 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 22500583207) ^ 102 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_23242647853 : Nat.Prime 23242647853 := by
  apply lucas_primality 23242647853 (2 : ZMod 23242647853)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (277, 1), (743, 1), (3137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (277, 1), (743, 1), (3137, 1)] : List FactorBlock).map factorBlockValue).prod) = 23242647853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_277
      · exact prime_oneHundredTwentyFourDR_743
      · exact prime_oneHundredTwentyFourDR_3137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23242647853) ^ 11621323926 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 23242647853) ^ 7747549284 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 23242647853) ^ 83908476 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 23242647853) ^ 31282164 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 23242647853) ^ 7409196 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_25928792959 : Nat.Prime 25928792959 := by
  apply lucas_primality 25928792959 (3 : ZMod 25928792959)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (21715907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (21715907, 1)] : List FactorBlock).map factorBlockValue).prod) = 25928792959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_199
      · exact prime_oneHundredTwentyFourDR_21715907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25928792959) ^ 12964396479 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 25928792959) ^ 8642930986 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 25928792959) ^ 130295442 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 25928792959) ^ 1194 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_26334580033 : Nat.Prime 26334580033 := by
  apply lucas_primality 26334580033 (7 : ZMod 26334580033)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (19, 1), (167, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (19, 1), (167, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) = 26334580033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_167
      · exact prime_oneHundredTwentyFourDR_1601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 26334580033) ^ 13167290016 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 26334580033) ^ 8778193344 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 26334580033) ^ 1386030528 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 26334580033) ^ 157692096 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 26334580033) ^ 16448832 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_31731525053 : Nat.Prime 31731525053 := by
  apply lucas_primality 31731525053 (2 : ZMod 31731525053)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (449, 1), (768169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (449, 1), (768169, 1)] : List FactorBlock).map factorBlockValue).prod) = 31731525053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_449
      · exact prime_oneHundredTwentyFourDR_768169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31731525053) ^ 15865762526 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 31731525053) ^ 1379631524 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 31731525053) ^ 70671548 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 31731525053) ^ 41308 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_33688806289 : Nat.Prime 33688806289 := by
  apply lucas_primality 33688806289 (11 : ZMod 33688806289)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (157, 1), (4470383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (157, 1), (4470383, 1)] : List FactorBlock).map factorBlockValue).prod) = 33688806289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_157
      · exact prime_oneHundredTwentyFourDR_4470383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33688806289) ^ 16844403144 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 33688806289) ^ 11229602096 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 33688806289) ^ 214578384 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 33688806289) ^ 7536 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_35864414309 : Nat.Prime 35864414309 := by
  apply lucas_primality 35864414309 (2 : ZMod 35864414309)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6229, 1), (1439413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6229, 1), (1439413, 1)] : List FactorBlock).map factorBlockValue).prod) = 35864414309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_6229
      · exact prime_oneHundredTwentyFourDR_1439413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35864414309) ^ 17932207154 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 35864414309) ^ 5757652 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 35864414309) ^ 24916 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_37426664851 : Nat.Prime 37426664851 := by
  apply lucas_primality 37426664851 (3 : ZMod 37426664851)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (29, 1), (8603831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (29, 1), (8603831, 1)] : List FactorBlock).map factorBlockValue).prod) = 37426664851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_29
      · exact prime_oneHundredTwentyFourDR_8603831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37426664851) ^ 18713332425 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 37426664851) ^ 12475554950 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 37426664851) ^ 7485332970 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 37426664851) ^ 1290574650 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 37426664851) ^ 4350 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_57999273037 : Nat.Prime 57999273037 := by
  apply lucas_primality 57999273037 (2 : ZMod 57999273037)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3313, 1), (1458881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3313, 1), (1458881, 1)] : List FactorBlock).map factorBlockValue).prod) = 57999273037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_3313
      · exact prime_oneHundredTwentyFourDR_1458881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57999273037) ^ 28999636518 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57999273037) ^ 19333091012 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57999273037) ^ 17506572 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 57999273037) ^ 39756 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_59032086229 : Nat.Prime 59032086229 := by
  apply lucas_primality 59032086229 (2 : ZMod 59032086229)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (60732599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (60732599, 1)] : List FactorBlock).map factorBlockValue).prod) = 59032086229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_60732599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59032086229) ^ 29516043114 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59032086229) ^ 19677362076 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 59032086229) ^ 972 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_64533688097 : Nat.Prime 64533688097 := by
  apply lucas_primality 64533688097 (3 : ZMod 64533688097)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2016677753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2016677753, 1)] : List FactorBlock).map factorBlockValue).prod) = 64533688097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_2016677753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 64533688097) ^ 32266844048 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 64533688097) ^ 32 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_66245230633 : Nat.Prime 66245230633 := by
  apply lucas_primality 66245230633 (15 : ZMod 66245230633)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (4007, 1), (98407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (4007, 1), (98407, 1)] : List FactorBlock).map factorBlockValue).prod) = 66245230633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_4007
      · exact prime_oneHundredTwentyFourDR_98407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 66245230633) ^ 33122615316 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (15 : ZMod 66245230633) ^ 22081743544 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (15 : ZMod 66245230633) ^ 9463604376 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (15 : ZMod 66245230633) ^ 16532376 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (15 : ZMod 66245230633) ^ 673176 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_74714424371 : Nat.Prime 74714424371 := by
  apply lucas_primality 74714424371 (10 : ZMod 74714424371)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7471442437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7471442437, 1)] : List FactorBlock).map factorBlockValue).prod) = 74714424371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_7471442437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 74714424371) ^ 37357212185 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 74714424371) ^ 14942884874 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 74714424371) ^ 10 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_75919713827 : Nat.Prime 75919713827 := by
  apply lucas_primality 75919713827 (2 : ZMod 75919713827)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (197, 1), (17517239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (197, 1), (17517239, 1)] : List FactorBlock).map factorBlockValue).prod) = 75919713827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_197
      · exact prime_oneHundredTwentyFourDR_17517239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75919713827) ^ 37959856913 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 75919713827) ^ 6901792166 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 75919713827) ^ 385379258 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 75919713827) ^ 4334 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_83910500809 : Nat.Prime 83910500809 := by
  apply lucas_primality 83910500809 (13 : ZMod 83910500809)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (337, 1), (10374691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (337, 1), (10374691, 1)] : List FactorBlock).map factorBlockValue).prod) = 83910500809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_337
      · exact prime_oneHundredTwentyFourDR_10374691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 83910500809) ^ 41955250404 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 83910500809) ^ 27970166936 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 83910500809) ^ 248992584 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 83910500809) ^ 8088 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_98047063403 : Nat.Prime 98047063403 := by
  apply lucas_primality 98047063403 (2 : ZMod 98047063403)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (67, 1), (5119, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (67, 1), (5119, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) = 98047063403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_67
      · exact prime_oneHundredTwentyFourDR_5119
      · exact prime_oneHundredTwentyFourDR_7523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98047063403) ^ 49023531701 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 98047063403) ^ 5160371758 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 98047063403) ^ 1463389006 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 98047063403) ^ 19153558 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 98047063403) ^ 13032974 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_105211804913 : Nat.Prime 105211804913 := by
  apply lucas_primality 105211804913 (3 : ZMod 105211804913)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (52529, 1), (125183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (52529, 1), (125183, 1)] : List FactorBlock).map factorBlockValue).prod) = 105211804913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_52529
      · exact prime_oneHundredTwentyFourDR_125183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 105211804913) ^ 52605902456 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 105211804913) ^ 2002928 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 105211804913) ^ 840464 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_126193865579 : Nat.Prime 126193865579 := by
  apply lucas_primality 126193865579 (2 : ZMod 126193865579)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (89, 1), (64450391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (89, 1), (64450391, 1)] : List FactorBlock).map factorBlockValue).prod) = 126193865579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_89
      · exact prime_oneHundredTwentyFourDR_64450391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 126193865579) ^ 63096932789 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 126193865579) ^ 11472169598 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 126193865579) ^ 1417908602 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 126193865579) ^ 1958 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_162104247727 : Nat.Prime 162104247727 := by
  apply lucas_primality 162104247727 (3 : ZMod 162104247727)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (139986397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (139986397, 1)] : List FactorBlock).map factorBlockValue).prod) = 162104247727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_193
      · exact prime_oneHundredTwentyFourDR_139986397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 162104247727) ^ 81052123863 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 162104247727) ^ 54034749242 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 162104247727) ^ 839918382 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 162104247727) ^ 1158 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_178847081891 : Nat.Prime 178847081891 := by
  apply lucas_primality 178847081891 (2 : ZMod 178847081891)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (3517, 1), (267643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (3517, 1), (267643, 1)] : List FactorBlock).map factorBlockValue).prod) = 178847081891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_3517
      · exact prime_oneHundredTwentyFourDR_267643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178847081891) ^ 89423540945 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 178847081891) ^ 35769416378 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 178847081891) ^ 9413004310 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 178847081891) ^ 50852170 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 178847081891) ^ 668230 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_196094126807 : Nat.Prime 196094126807 := by
  apply lucas_primality 196094126807 (5 : ZMod 196094126807)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (98047063403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (98047063403, 1)] : List FactorBlock).map factorBlockValue).prod) = 196094126807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_98047063403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 196094126807) ^ 98047063403 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 196094126807) ^ 2 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_198287473073 : Nat.Prime 198287473073 := by
  apply lucas_primality 198287473073 (3 : ZMod 198287473073)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (953305159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (953305159, 1)] : List FactorBlock).map factorBlockValue).prod) = 198287473073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_953305159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 198287473073) ^ 99143736536 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 198287473073) ^ 15252882544 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 198287473073) ^ 208 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_209261502889 : Nat.Prime 209261502889 := by
  apply lucas_primality 209261502889 (7 : ZMod 209261502889)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8719229287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8719229287, 1)] : List FactorBlock).map factorBlockValue).prod) = 209261502889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_8719229287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 209261502889) ^ 104630751444 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 209261502889) ^ 69753834296 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 209261502889) ^ 24 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_220367657329 : Nat.Prime 220367657329 := by
  apply lucas_primality 220367657329 (11 : ZMod 220367657329)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (13, 1), (83, 1), (607837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (13, 1), (83, 1), (607837, 1)] : List FactorBlock).map factorBlockValue).prod) = 220367657329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_83
      · exact prime_oneHundredTwentyFourDR_607837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 220367657329) ^ 110183828664 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 220367657329) ^ 73455885776 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 220367657329) ^ 31481093904 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 220367657329) ^ 16951358256 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 220367657329) ^ 2655032016 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 220367657329) ^ 362544 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_392335787633 : Nat.Prime 392335787633 := by
  apply lucas_primality 392335787633 (3 : ZMod 392335787633)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (41, 1), (16164131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (41, 1), (16164131, 1)] : List FactorBlock).map factorBlockValue).prod) = 392335787633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_41
      · exact prime_oneHundredTwentyFourDR_16164131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 392335787633) ^ 196167893816 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 392335787633) ^ 10603669936 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 392335787633) ^ 9569165552 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 392335787633) ^ 24272 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_405656299421 : Nat.Prime 405656299421 := by
  apply lucas_primality 405656299421 (2 : ZMod 405656299421)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (1193106763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (1193106763, 1)] : List FactorBlock).map factorBlockValue).prod) = 405656299421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_1193106763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 405656299421) ^ 202828149710 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 405656299421) ^ 81131259884 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 405656299421) ^ 23862135260 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 405656299421) ^ 340 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_556294533517 : Nat.Prime 556294533517 := by
  apply lucas_primality 556294533517 (2 : ZMod 556294533517)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (709, 1), (1487, 1), (14657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (709, 1), (1487, 1), (14657, 1)] : List FactorBlock).map factorBlockValue).prod) = 556294533517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_709
      · exact prime_oneHundredTwentyFourDR_1487
      · exact prime_oneHundredTwentyFourDR_14657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 556294533517) ^ 278147266758 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 556294533517) ^ 185431511172 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 556294533517) ^ 784618524 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 556294533517) ^ 374105268 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 556294533517) ^ 37954188 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_597256891963 : Nat.Prime 597256891963 := by
  apply lucas_primality 597256891963 (2 : ZMod 597256891963)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (97, 1), (21834353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (97, 1), (21834353, 1)] : List FactorBlock).map factorBlockValue).prod) = 597256891963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_47
      · exact prime_oneHundredTwentyFourDR_97
      · exact prime_oneHundredTwentyFourDR_21834353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 597256891963) ^ 298628445981 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 597256891963) ^ 199085630654 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 597256891963) ^ 12707593446 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 597256891963) ^ 6157287546 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 597256891963) ^ 27354 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_865553648809 : Nat.Prime 865553648809 := by
  apply lucas_primality 865553648809 (7 : ZMod 865553648809)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (523, 1), (68957429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (523, 1), (68957429, 1)] : List FactorBlock).map factorBlockValue).prod) = 865553648809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_523
      · exact prime_oneHundredTwentyFourDR_68957429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 865553648809) ^ 432776824404 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 865553648809) ^ 288517882936 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 865553648809) ^ 1654978296 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 865553648809) ^ 12552 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_881470629317 : Nat.Prime 881470629317 := by
  apply lucas_primality 881470629317 (2 : ZMod 881470629317)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (220367657329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (220367657329, 1)] : List FactorBlock).map factorBlockValue).prod) = 881470629317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_220367657329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 881470629317) ^ 440735314658 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 881470629317) ^ 4 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1097665567571 : Nat.Prime 1097665567571 := by
  apply lucas_primality 1097665567571 (2 : ZMod 1097665567571)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 2), (131, 1), (167, 1), (2699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 2), (131, 1), (167, 1), (2699, 1)] : List FactorBlock).map factorBlockValue).prod) = 1097665567571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_131
      · exact prime_oneHundredTwentyFourDR_167
      · exact prime_oneHundredTwentyFourDR_2699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1097665567571) ^ 548832783785 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097665567571) ^ 219533113514 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097665567571) ^ 99787778870 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097665567571) ^ 84435812890 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097665567571) ^ 8379126470 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097665567571) ^ 6572847710 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097665567571) ^ 406693430 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1214717881457 : Nat.Prime 1214717881457 := by
  apply lucas_primality 1214717881457 (3 : ZMod 1214717881457)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (127, 1), (1657, 1), (360769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (127, 1), (1657, 1), (360769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1214717881457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_127
      · exact prime_oneHundredTwentyFourDR_1657
      · exact prime_oneHundredTwentyFourDR_360769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1214717881457) ^ 607358940728 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1214717881457) ^ 9564707728 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1214717881457) ^ 733082608 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1214717881457) ^ 3367024 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1367234409419 : Nat.Prime 1367234409419 := by
  apply lucas_primality 1367234409419 (2 : ZMod 1367234409419)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (58193, 1), (11747413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (58193, 1), (11747413, 1)] : List FactorBlock).map factorBlockValue).prod) = 1367234409419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_58193
      · exact prime_oneHundredTwentyFourDR_11747413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1367234409419) ^ 683617204709 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1367234409419) ^ 23494826 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1367234409419) ^ 116386 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1741983823259 : Nat.Prime 1741983823259 := by
  apply lucas_primality 1741983823259 (6 : ZMod 1741983823259)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (181, 1), (2477, 1), (277531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (181, 1), (2477, 1), (277531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1741983823259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_181
      · exact prime_oneHundredTwentyFourDR_2477
      · exact prime_oneHundredTwentyFourDR_277531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1741983823259) ^ 870991911629 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1741983823259) ^ 248854831894 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1741983823259) ^ 9624220018 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1741983823259) ^ 703263554 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1741983823259) ^ 6276718 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1931920823563 : Nat.Prime 1931920823563 := by
  apply lucas_primality 1931920823563 (2 : ZMod 1931920823563)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (18940400231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (18940400231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1931920823563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_18940400231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1931920823563) ^ 965960411781 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931920823563) ^ 643973607854 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931920823563) ^ 113642401386 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931920823563) ^ 102 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1933828254263 : Nat.Prime 1933828254263 := by
  apply lucas_primality 1933828254263 (5 : ZMod 1933828254263)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (8556762187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (8556762187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1933828254263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_113
      · exact prime_oneHundredTwentyFourDR_8556762187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1933828254263) ^ 966914127131 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1933828254263) ^ 17113524374 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1933828254263) ^ 226 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2063569989203 : Nat.Prime 2063569989203 := by
  apply lucas_primality 2063569989203 (2 : ZMod 2063569989203)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (281, 1), (977, 1), (3758273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (281, 1), (977, 1), (3758273, 1)] : List FactorBlock).map factorBlockValue).prod) = 2063569989203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_281
      · exact prime_oneHundredTwentyFourDR_977
      · exact prime_oneHundredTwentyFourDR_3758273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2063569989203) ^ 1031784994601 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2063569989203) ^ 7343665442 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2063569989203) ^ 2112149426 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2063569989203) ^ 549074 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2388219450997 : Nat.Prime 2388219450997 := by
  apply lucas_primality 2388219450997 (2 : ZMod 2388219450997)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (997, 1), (2811509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (997, 1), (2811509, 1)] : List FactorBlock).map factorBlockValue).prod) = 2388219450997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_71
      · exact prime_oneHundredTwentyFourDR_997
      · exact prime_oneHundredTwentyFourDR_2811509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2388219450997) ^ 1194109725498 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2388219450997) ^ 796073150332 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2388219450997) ^ 33636893676 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2388219450997) ^ 2395405668 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2388219450997) ^ 849444 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_3487470611201 : Nat.Prime 3487470611201 := by
  apply lucas_primality 3487470611201 (3 : ZMod 3487470611201)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 2), (19, 1), (28679857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 2), (19, 1), (28679857, 1)] : List FactorBlock).map factorBlockValue).prod) = 3487470611201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_28679857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3487470611201) ^ 1743735305600 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3487470611201) ^ 697494122240 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3487470611201) ^ 183551084800 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3487470611201) ^ 121600 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_4034982851729 : Nat.Prime 4034982851729 := by
  apply lucas_primality 4034982851729 (3 : ZMod 4034982851729)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (13272969907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (13272969907, 1)] : List FactorBlock).map factorBlockValue).prod) = 4034982851729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_13272969907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4034982851729) ^ 2017491425864 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4034982851729) ^ 212367518512 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4034982851729) ^ 304 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_4881148959241 : Nat.Prime 4881148959241 := by
  apply lucas_primality 4881148959241 (19 : ZMod 4881148959241)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (31, 1), (41, 1), (137, 1), (77867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (31, 1), (41, 1), (137, 1), (77867, 1)] : List FactorBlock).map factorBlockValue).prod) = 4881148959241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_41
      · exact prime_oneHundredTwentyFourDR_137
      · exact prime_oneHundredTwentyFourDR_77867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 4881148959241) ^ 2440574479620 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 4881148959241) ^ 1627049653080 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 4881148959241) ^ 976229791848 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 4881148959241) ^ 157456418040 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 4881148959241) ^ 119052413640 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 4881148959241) ^ 35628824520 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 4881148959241) ^ 62685720 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_6990964227089 : Nat.Prime 6990964227089 := by
  apply lucas_primality 6990964227089 (3 : ZMod 6990964227089)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (239857, 1), (1821649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (239857, 1), (1821649, 1)] : List FactorBlock).map factorBlockValue).prod) = 6990964227089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_239857
      · exact prime_oneHundredTwentyFourDR_1821649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6990964227089) ^ 3495482113544 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6990964227089) ^ 29146384 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6990964227089) ^ 3837712 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_8942359683779 : Nat.Prime 8942359683779 := by
  apply lucas_primality 8942359683779 (2 : ZMod 8942359683779)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (457789, 1), (9766901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (457789, 1), (9766901, 1)] : List FactorBlock).map factorBlockValue).prod) = 8942359683779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_457789
      · exact prime_oneHundredTwentyFourDR_9766901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8942359683779) ^ 4471179841889 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8942359683779) ^ 19533802 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8942359683779) ^ 915578 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_11054238359569 : Nat.Prime 11054238359569 := by
  apply lucas_primality 11054238359569 (7 : ZMod 11054238359569)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (61, 1), (131, 1), (967, 1), (29803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (61, 1), (131, 1), (967, 1), (29803, 1)] : List FactorBlock).map factorBlockValue).prod) = 11054238359569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_61
      · exact prime_oneHundredTwentyFourDR_131
      · exact prime_oneHundredTwentyFourDR_967
      · exact prime_oneHundredTwentyFourDR_29803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11054238359569) ^ 5527119179784 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 11054238359569) ^ 3684746119856 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 11054238359569) ^ 181217022288 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 11054238359569) ^ 84383498928 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 11054238359569) ^ 11431477104 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 11054238359569) ^ 370910256 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_12468199459721 : Nat.Prime 12468199459721 := by
  apply lucas_primality 12468199459721 (3 : ZMod 12468199459721)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (97, 1), (3213453469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (97, 1), (3213453469, 1)] : List FactorBlock).map factorBlockValue).prod) = 12468199459721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_97
      · exact prime_oneHundredTwentyFourDR_3213453469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12468199459721) ^ 6234099729860 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 12468199459721) ^ 2493639891944 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 12468199459721) ^ 128538138760 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 12468199459721) ^ 3880 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_13217372915987 : Nat.Prime 13217372915987 := by
  apply lucas_primality 13217372915987 (2 : ZMod 13217372915987)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (641, 1), (10309963273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (641, 1), (10309963273, 1)] : List FactorBlock).map factorBlockValue).prod) = 13217372915987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_641
      · exact prime_oneHundredTwentyFourDR_10309963273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13217372915987) ^ 6608686457993 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13217372915987) ^ 20619926546 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 13217372915987) ^ 1282 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_15326452682269 : Nat.Prime 15326452682269 := by
  apply lucas_primality 15326452682269 (10 : ZMod 15326452682269)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (31, 1), (452748809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (31, 1), (452748809, 1)] : List FactorBlock).map factorBlockValue).prod) = 15326452682269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_452748809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 15326452682269) ^ 7663226341134 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 15326452682269) ^ 5108817560756 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 15326452682269) ^ 2189493240324 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 15326452682269) ^ 1178957898636 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 15326452682269) ^ 494401699428 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 15326452682269) ^ 33852 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_20541412985911 : Nat.Prime 20541412985911 := by
  apply lucas_primality 20541412985911 (3 : ZMod 20541412985911)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (305479, 1), (2241443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (305479, 1), (2241443, 1)] : List FactorBlock).map factorBlockValue).prod) = 20541412985911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_305479
      · exact prime_oneHundredTwentyFourDR_2241443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20541412985911) ^ 10270706492955 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20541412985911) ^ 6847137661970 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20541412985911) ^ 4108282597182 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20541412985911) ^ 67243290 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20541412985911) ^ 9164370 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_42662980614607 : Nat.Prime 42662980614607 := by
  apply lucas_primality 42662980614607 (5 : ZMod 42662980614607)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (457, 1), (809, 1), (1748407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (457, 1), (809, 1), (1748407, 1)] : List FactorBlock).map factorBlockValue).prod) = 42662980614607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_457
      · exact prime_oneHundredTwentyFourDR_809
      · exact prime_oneHundredTwentyFourDR_1748407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 42662980614607) ^ 21331490307303 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 42662980614607) ^ 14220993538202 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 42662980614607) ^ 3878452783146 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 42662980614607) ^ 93354443358 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 42662980614607) ^ 52735451934 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 42662980614607) ^ 24401058 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_44216953438277 : Nat.Prime 44216953438277 := by
  apply lucas_primality 44216953438277 (2 : ZMod 44216953438277)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11054238359569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11054238359569, 1)] : List FactorBlock).map factorBlockValue).prod) = 44216953438277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_11054238359569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 44216953438277) ^ 22108476719138 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44216953438277) ^ 4 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_50553014800571 : Nat.Prime 50553014800571 := by
  apply lucas_primality 50553014800571 (2 : ZMod 50553014800571)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (211, 1), (557180809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (211, 1), (557180809, 1)] : List FactorBlock).map factorBlockValue).prod) = 50553014800571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_43
      · exact prime_oneHundredTwentyFourDR_211
      · exact prime_oneHundredTwentyFourDR_557180809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50553014800571) ^ 25276507400285 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 50553014800571) ^ 10110602960114 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 50553014800571) ^ 1175651506990 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 50553014800571) ^ 239587747870 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 50553014800571) ^ 90730 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_63554098052927 : Nat.Prime 63554098052927 := by
  apply lucas_primality 63554098052927 (5 : ZMod 63554098052927)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (743, 1), (1291, 1), (2548327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (743, 1), (1291, 1), (2548327, 1)] : List FactorBlock).map factorBlockValue).prod) = 63554098052927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_743
      · exact prime_oneHundredTwentyFourDR_1291
      · exact prime_oneHundredTwentyFourDR_2548327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 63554098052927) ^ 31777049026463 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 63554098052927) ^ 4888776773302 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 63554098052927) ^ 85537144082 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 63554098052927) ^ 49228580986 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 63554098052927) ^ 24939538 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_64360559390279 : Nat.Prime 64360559390279 := by
  apply lucas_primality 64360559390279 (17 : ZMod 64360559390279)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (149, 1), (1493, 1), (2159081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (149, 1), (1493, 1), (2159081, 1)] : List FactorBlock).map factorBlockValue).prod) = 64360559390279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_67
      · exact prime_oneHundredTwentyFourDR_149
      · exact prime_oneHundredTwentyFourDR_1493
      · exact prime_oneHundredTwentyFourDR_2159081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 64360559390279) ^ 32180279695139 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 64360559390279) ^ 960605364034 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 64360559390279) ^ 431950063022 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 64360559390279) ^ 43108211246 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 64360559390279) ^ 29809238 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_88484797934443 : Nat.Prime 88484797934443 := by
  apply lucas_primality 88484797934443 (2 : ZMod 88484797934443)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (131, 1), (149, 1), (2767561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (131, 1), (149, 1), (2767561, 1)] : List FactorBlock).map factorBlockValue).prod) = 88484797934443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_131
      · exact prime_oneHundredTwentyFourDR_149
      · exact prime_oneHundredTwentyFourDR_2767561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88484797934443) ^ 44242398967221 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 88484797934443) ^ 29494932644814 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 88484797934443) ^ 12640685419206 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 88484797934443) ^ 6806522918034 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 88484797934443) ^ 675456472782 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 88484797934443) ^ 593857704258 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 88484797934443) ^ 31972122 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_105060044122301 : Nat.Prime 105060044122301 := by
  apply lucas_primality 105060044122301 (2 : ZMod 105060044122301)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (71, 1), (14797189313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (71, 1), (14797189313, 1)] : List FactorBlock).map factorBlockValue).prod) = 105060044122301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_71
      · exact prime_oneHundredTwentyFourDR_14797189313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105060044122301) ^ 52530022061150 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105060044122301) ^ 21012008824460 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105060044122301) ^ 1479718931300 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105060044122301) ^ 7100 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_120773054768837 : Nat.Prime 120773054768837 := by
  apply lucas_primality 120773054768837 (2 : ZMod 120773054768837)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2397133, 1), (12595573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2397133, 1), (12595573, 1)] : List FactorBlock).map factorBlockValue).prod) = 120773054768837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_2397133
      · exact prime_oneHundredTwentyFourDR_12595573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120773054768837) ^ 60386527384418 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 120773054768837) ^ 50382292 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 120773054768837) ^ 9588532 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_142363093773557 : Nat.Prime 142363093773557 := by
  apply lucas_primality 142363093773557 (2 : ZMod 142363093773557)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1697, 1), (5233, 1), (4007789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1697, 1), (5233, 1), (4007789, 1)] : List FactorBlock).map factorBlockValue).prod) = 142363093773557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_1697
      · exact prime_oneHundredTwentyFourDR_5233
      · exact prime_oneHundredTwentyFourDR_4007789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142363093773557) ^ 71181546886778 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 142363093773557) ^ 83891039348 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 142363093773557) ^ 27204871732 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 142363093773557) ^ 35521604 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_149281518186929 : Nat.Prime 149281518186929 := by
  apply lucas_primality 149281518186929 (3 : ZMod 149281518186929)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (405656299421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (405656299421, 1)] : List FactorBlock).map factorBlockValue).prod) = 149281518186929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_405656299421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 149281518186929) ^ 74640759093464 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 149281518186929) ^ 6490500790736 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 149281518186929) ^ 368 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_200817242429329 : Nat.Prime 200817242429329 := by
  apply lucas_primality 200817242429329 (26 : ZMod 200817242429329)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (19, 1), (18701, 1), (560689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (19, 1), (18701, 1), (560689, 1)] : List FactorBlock).map factorBlockValue).prod) = 200817242429329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_18701
      · exact prime_oneHundredTwentyFourDR_560689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 200817242429329) ^ 100408621214664 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (26 : ZMod 200817242429329) ^ 66939080809776 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (26 : ZMod 200817242429329) ^ 28688177489904 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (26 : ZMod 200817242429329) ^ 10569328548912 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (26 : ZMod 200817242429329) ^ 10738315728 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (26 : ZMod 200817242429329) ^ 358161552 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_10789
      · exact prime_oneHundredTwentyFourDR_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_375043386305381 : Nat.Prime 375043386305381 := by
  apply lucas_primality 375043386305381 (2 : ZMod 375043386305381)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (19, 1), (75919713827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (19, 1), (75919713827, 1)] : List FactorBlock).map factorBlockValue).prod) = 375043386305381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_75919713827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 375043386305381) ^ 187521693152690 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 375043386305381) ^ 75008677261076 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 375043386305381) ^ 28849491254260 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 375043386305381) ^ 19739125595020 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 375043386305381) ^ 4940 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_411578332088453 : Nat.Prime 411578332088453 := by
  apply lucas_primality 411578332088453 (2 : ZMod 411578332088453)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (227, 1), (9644257477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (227, 1), (9644257477, 1)] : List FactorBlock).map factorBlockValue).prod) = 411578332088453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_47
      · exact prime_oneHundredTwentyFourDR_227
      · exact prime_oneHundredTwentyFourDR_9644257477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 411578332088453) ^ 205789166044226 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 411578332088453) ^ 8756985789116 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 411578332088453) ^ 1813120405676 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 411578332088453) ^ 42676 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_422544030970343 : Nat.Prime 422544030970343 := by
  apply lucas_primality 422544030970343 (5 : ZMod 422544030970343)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (1877, 1), (1541895151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (1877, 1), (1541895151, 1)] : List FactorBlock).map factorBlockValue).prod) = 422544030970343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_73
      · exact prime_oneHundredTwentyFourDR_1877
      · exact prime_oneHundredTwentyFourDR_1541895151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 422544030970343) ^ 211272015485171 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 422544030970343) ^ 5788274396854 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 422544030970343) ^ 225116692046 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 422544030970343) ^ 274042 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_474525715304651 : Nat.Prime 474525715304651 := by
  apply lucas_primality 474525715304651 (2 : ZMod 474525715304651)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (937, 1), (10128617189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (937, 1), (10128617189, 1)] : List FactorBlock).map factorBlockValue).prod) = 474525715304651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_937
      · exact prime_oneHundredTwentyFourDR_10128617189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 474525715304651) ^ 237262857652325 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 474525715304651) ^ 94905143060930 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 474525715304651) ^ 506430859450 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 474525715304651) ^ 46850 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_590632866122687 : Nat.Prime 590632866122687 := by
  apply lucas_primality 590632866122687 (5 : ZMod 590632866122687)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (311, 1), (2141, 1), (443517293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (311, 1), (2141, 1), (443517293, 1)] : List FactorBlock).map factorBlockValue).prod) = 590632866122687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_311
      · exact prime_oneHundredTwentyFourDR_2141
      · exact prime_oneHundredTwentyFourDR_443517293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 590632866122687) ^ 295316433061343 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 590632866122687) ^ 1899141048626 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 590632866122687) ^ 275867756246 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 590632866122687) ^ 1331702 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_639939235066399 : Nat.Prime 639939235066399 := by
  apply lucas_primality 639939235066399 (3 : ZMod 639939235066399)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (137, 1), (75169, 1), (3452287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (137, 1), (75169, 1), (3452287, 1)] : List FactorBlock).map factorBlockValue).prod) = 639939235066399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_137
      · exact prime_oneHundredTwentyFourDR_75169
      · exact prime_oneHundredTwentyFourDR_3452287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 639939235066399) ^ 319969617533199 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 639939235066399) ^ 213313078355466 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 639939235066399) ^ 4671089307054 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 639939235066399) ^ 8513339742 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 639939235066399) ^ 185366754 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_670922381031467 : Nat.Prime 670922381031467 := by
  apply lucas_primality 670922381031467 (2 : ZMod 670922381031467)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (83, 1), (223, 1), (593, 1), (1608611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (83, 1), (223, 1), (593, 1), (1608611, 1)] : List FactorBlock).map factorBlockValue).prod) = 670922381031467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_83
      · exact prime_oneHundredTwentyFourDR_223
      · exact prime_oneHundredTwentyFourDR_593
      · exact prime_oneHundredTwentyFourDR_1608611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 670922381031467) ^ 335461190515733 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 670922381031467) ^ 35311704264814 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 670922381031467) ^ 8083402181102 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 670922381031467) ^ 3008620542742 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 670922381031467) ^ 1131403677962 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 670922381031467) ^ 417081806 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_697646239727291 : Nat.Prime 697646239727291 := by
  apply lucas_primality 697646239727291 (2 : ZMod 697646239727291)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (277, 1), (11437, 1), (3145903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (277, 1), (11437, 1), (3145903, 1)] : List FactorBlock).map factorBlockValue).prod) = 697646239727291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_277
      · exact prime_oneHundredTwentyFourDR_11437
      · exact prime_oneHundredTwentyFourDR_3145903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 697646239727291) ^ 348823119863645 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 697646239727291) ^ 139529247945458 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 697646239727291) ^ 99663748532470 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 697646239727291) ^ 2518578482770 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 697646239727291) ^ 60999059170 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 697646239727291) ^ 221763430 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_841135460775667 : Nat.Prime 841135460775667 := by
  apply lucas_primality 841135460775667 (3 : ZMod 841135460775667)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (101, 1), (198287473073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (101, 1), (198287473073, 1)] : List FactorBlock).map factorBlockValue).prod) = 841135460775667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_101
      · exact prime_oneHundredTwentyFourDR_198287473073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 841135460775667) ^ 420567730387833 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841135460775667) ^ 280378486925222 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841135460775667) ^ 120162208682238 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841135460775667) ^ 8328073869066 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841135460775667) ^ 4242 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_935754265906067 : Nat.Prime 935754265906067 := by
  apply lucas_primality 935754265906067 (2 : ZMod 935754265906067)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (177223, 1), (24220619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (177223, 1), (24220619, 1)] : List FactorBlock).map factorBlockValue).prod) = 935754265906067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_109
      · exact prime_oneHundredTwentyFourDR_177223
      · exact prime_oneHundredTwentyFourDR_24220619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 935754265906067) ^ 467877132953033 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 935754265906067) ^ 8584901522074 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 935754265906067) ^ 5280094942 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 935754265906067) ^ 38634614 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1072265153536007 : Nat.Prime 1072265153536007 := by
  apply lucas_primality 1072265153536007 (5 : ZMod 1072265153536007)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (12468199459721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (12468199459721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1072265153536007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_43
      · exact prime_oneHundredTwentyFourDR_12468199459721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1072265153536007) ^ 536132576768003 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1072265153536007) ^ 24936398919442 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1072265153536007) ^ 86 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1190350807521041 : Nat.Prime 1190350807521041 := by
  apply lucas_primality 1190350807521041 (3 : ZMod 1190350807521041)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (31, 1), (463, 1), (94243111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (31, 1), (463, 1), (94243111, 1)] : List FactorBlock).map factorBlockValue).prod) = 1190350807521041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_463
      · exact prime_oneHundredTwentyFourDR_94243111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1190350807521041) ^ 595175403760520 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190350807521041) ^ 238070161504208 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190350807521041) ^ 108213709774640 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190350807521041) ^ 38398413145840 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190350807521041) ^ 2570952068080 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1190350807521041) ^ 12630640 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1366167123042079 : Nat.Prime 1366167123042079 := by
  apply lucas_primality 1366167123042079 (3 : ZMod 1366167123042079)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (37, 1), (199, 1), (152335717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (37, 1), (199, 1), (152335717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1366167123042079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_29
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_199
      · exact prime_oneHundredTwentyFourDR_152335717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1366167123042079) ^ 683083561521039 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1366167123042079) ^ 455389041014026 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1366167123042079) ^ 195166731863154 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1366167123042079) ^ 47109211139382 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1366167123042079) ^ 36923435757894 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1366167123042079) ^ 6865161422322 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1366167123042079) ^ 8968134 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1651596952044409 : Nat.Prime 1651596952044409 := by
  apply lucas_primality 1651596952044409 (13 : ZMod 1651596952044409)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (421, 1), (5281, 1), (754937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (421, 1), (5281, 1), (754937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1651596952044409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_41
      · exact prime_oneHundredTwentyFourDR_421
      · exact prime_oneHundredTwentyFourDR_5281
      · exact prime_oneHundredTwentyFourDR_754937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1651596952044409) ^ 825798476022204 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 1651596952044409) ^ 550532317348136 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 1651596952044409) ^ 40282852488888 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 1651596952044409) ^ 3923033140248 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 1651596952044409) ^ 312743221368 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 1651596952044409) ^ 2187728184 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1888174374868783 : Nat.Prime 1888174374868783 := by
  apply lucas_primality 1888174374868783 (5 : ZMod 1888174374868783)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 3), (13, 1), (71, 1), (2207, 1), (5527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 3), (13, 1), (71, 1), (2207, 1), (5527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1888174374868783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_71
      · exact prime_oneHundredTwentyFourDR_2207
      · exact prime_oneHundredTwentyFourDR_5527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1888174374868783) ^ 944087187434391 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1888174374868783) ^ 629391458289594 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1888174374868783) ^ 269739196409826 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1888174374868783) ^ 171652215897162 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1888174374868783) ^ 145244182682214 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1888174374868783) ^ 26594005279842 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1888174374868783) ^ 855538910226 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1888174374868783) ^ 341627352066 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2337532415679887 : Nat.Prime 2337532415679887 := by
  apply lucas_primality 2337532415679887 (5 : ZMod 2337532415679887)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (6089, 1), (7307, 1), (75703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (6089, 1), (7307, 1), (75703, 1)] : List FactorBlock).map factorBlockValue).prod) = 2337532415679887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_347
      · exact prime_oneHundredTwentyFourDR_6089
      · exact prime_oneHundredTwentyFourDR_7307
      · exact prime_oneHundredTwentyFourDR_75703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2337532415679887) ^ 1168766207839943 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2337532415679887) ^ 6736404656138 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2337532415679887) ^ 383894303774 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2337532415679887) ^ 319903163498 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2337532415679887) ^ 30877672162 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2380701615042083 : Nat.Prime 2380701615042083 := by
  apply lucas_primality 2380701615042083 (2 : ZMod 2380701615042083)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1190350807521041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1190350807521041, 1)] : List FactorBlock).map factorBlockValue).prod) = 2380701615042083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_1190350807521041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2380701615042083) ^ 1190350807521041 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2380701615042083) ^ 2 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2476149392543513 : Nat.Prime 2476149392543513 := by
  apply lucas_primality 2476149392543513 (3 : ZMod 2476149392543513)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (44216953438277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (44216953438277, 1)] : List FactorBlock).map factorBlockValue).prod) = 2476149392543513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_44216953438277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2476149392543513) ^ 1238074696271756 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2476149392543513) ^ 353735627506216 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2476149392543513) ^ 56 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_3767362811129249 : Nat.Prime 3767362811129249 := by
  apply lucas_primality 3767362811129249 (3 : ZMod 3767362811129249)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 2), (457, 1), (486985013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 2), (457, 1), (486985013, 1)] : List FactorBlock).map factorBlockValue).prod) = 3767362811129249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_457
      · exact prime_oneHundredTwentyFourDR_486985013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3767362811129249) ^ 1883681405564624 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3767362811129249) ^ 163798383092576 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3767362811129249) ^ 8243682300064 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3767362811129249) ^ 7736096 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_5581169917818329 : Nat.Prime 5581169917818329 := by
  apply lucas_primality 5581169917818329 (3 : ZMod 5581169917818329)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (697646239727291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (697646239727291, 1)] : List FactorBlock).map factorBlockValue).prod) = 5581169917818329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_697646239727291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5581169917818329) ^ 2790584958909164 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5581169917818329) ^ 8 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_6584759398665493 : Nat.Prime 6584759398665493 := by
  apply lucas_primality 6584759398665493 (2 : ZMod 6584759398665493)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (773, 1), (64533688097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (773, 1), (64533688097, 1)] : List FactorBlock).map factorBlockValue).prod) = 6584759398665493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_773
      · exact prime_oneHundredTwentyFourDR_64533688097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6584759398665493) ^ 3292379699332746 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6584759398665493) ^ 2194919799555164 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6584759398665493) ^ 598614490787772 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6584759398665493) ^ 8518446828804 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6584759398665493) ^ 102036 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_6787962576035033 : Nat.Prime 6787962576035033 := by
  apply lucas_primality 6787962576035033 (3 : ZMod 6787962576035033)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (163, 1), (91753, 1), (8104823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (163, 1), (91753, 1), (8104823, 1)] : List FactorBlock).map factorBlockValue).prod) = 6787962576035033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_163
      · exact prime_oneHundredTwentyFourDR_91753
      · exact prime_oneHundredTwentyFourDR_8104823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6787962576035033) ^ 3393981288017516 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6787962576035033) ^ 969708939433576 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6787962576035033) ^ 41643942184264 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6787962576035033) ^ 73980824344 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6787962576035033) ^ 837521384 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_11513662460653469 : Nat.Prime 11513662460653469 := by
  apply lucas_primality 11513662460653469 (2 : ZMod 11513662460653469)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103, 1), (229267, 1), (121891867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103, 1), (229267, 1), (121891867, 1)] : List FactorBlock).map factorBlockValue).prod) = 11513662460653469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_103
      · exact prime_oneHundredTwentyFourDR_229267
      · exact prime_oneHundredTwentyFourDR_121891867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11513662460653469) ^ 5756831230326734 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11513662460653469) ^ 111783130685956 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11513662460653469) ^ 50219449204 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11513662460653469) ^ 94458004 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_12243562450529569 : Nat.Prime 12243562450529569 := by
  apply lucas_primality 12243562450529569 (14 : ZMod 12243562450529569)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 3), (103, 1), (809, 1), (311533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 3), (103, 1), (809, 1), (311533, 1)] : List FactorBlock).map factorBlockValue).prod) = 12243562450529569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_103
      · exact prime_oneHundredTwentyFourDR_809
      · exact prime_oneHundredTwentyFourDR_311533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 12243562450529569) ^ 6121781225264784 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (14 : ZMod 12243562450529569) ^ 4081187483509856 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (14 : ZMod 12243562450529569) ^ 720209555913504 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (14 : ZMod 12243562450529569) ^ 118869538354656 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (14 : ZMod 12243562450529569) ^ 15134193387552 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (14 : ZMod 12243562450529569) ^ 39301012896 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_21861718784556967 : Nat.Prime 21861718784556967 := by
  apply lucas_primality 21861718784556967 (3 : ZMod 21861718784556967)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (237343, 1), (31784069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (237343, 1), (31784069, 1)] : List FactorBlock).map factorBlockValue).prod) = 21861718784556967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_237343
      · exact prime_oneHundredTwentyFourDR_31784069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21861718784556967) ^ 10930859392278483 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21861718784556967) ^ 7287239594852322 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21861718784556967) ^ 3123102683508138 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21861718784556967) ^ 950509512372042 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21861718784556967) ^ 92110231962 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 21861718784556967) ^ 687820014 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_25294531025064947 : Nat.Prime 25294531025064947 := by
  apply lucas_primality 25294531025064947 (2 : ZMod 25294531025064947)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199, 1), (63554098052927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199, 1), (63554098052927, 1)] : List FactorBlock).map factorBlockValue).prod) = 25294531025064947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_199
      · exact prime_oneHundredTwentyFourDR_63554098052927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25294531025064947) ^ 12647265512532473 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 25294531025064947) ^ 127108196105854 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 25294531025064947) ^ 398 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_62562347515013051 : Nat.Prime 62562347515013051 := by
  apply lucas_primality 62562347515013051 (2 : ZMod 62562347515013051)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1439, 1), (11489, 1), (75683291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1439, 1), (11489, 1), (75683291, 1)] : List FactorBlock).map factorBlockValue).prod) = 62562347515013051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_1439
      · exact prime_oneHundredTwentyFourDR_11489
      · exact prime_oneHundredTwentyFourDR_75683291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62562347515013051) ^ 31281173757506525 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 62562347515013051) ^ 12512469503002610 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 62562347515013051) ^ 43476266514950 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 62562347515013051) ^ 5445412787450 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 62562347515013051) ^ 826633550 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_95031476064490463 : Nat.Prime 95031476064490463 := by
  apply lucas_primality 95031476064490463 (7 : ZMod 95031476064490463)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6787962576035033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6787962576035033, 1)] : List FactorBlock).map factorBlockValue).prod) = 95031476064490463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_6787962576035033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 95031476064490463) ^ 47515738032245231 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 95031476064490463) ^ 13575925152070066 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 95031476064490463) ^ 14 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_105717946992070201 : Nat.Prime 105717946992070201 := by
  apply lucas_primality 105717946992070201 (7 : ZMod 105717946992070201)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (53, 1), (5651, 1), (588296539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (53, 1), (5651, 1), (588296539, 1)] : List FactorBlock).map factorBlockValue).prod) = 105717946992070201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_53
      · exact prime_oneHundredTwentyFourDR_5651
      · exact prime_oneHundredTwentyFourDR_588296539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 105717946992070201) ^ 52858973496035100 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 105717946992070201) ^ 35239315664023400 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 105717946992070201) ^ 21143589398414040 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 105717946992070201) ^ 1994678245133400 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 105717946992070201) ^ 18707829940200 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 105717946992070201) ^ 179701800 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_126079869173764313 : Nat.Prime 126079869173764313 := by
  apply lucas_primality 126079869173764313 (3 : ZMod 126079869173764313)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (1361, 1), (274069, 1), (630613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (1361, 1), (274069, 1), (630613, 1)] : List FactorBlock).map factorBlockValue).prod) = 126079869173764313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_67
      · exact prime_oneHundredTwentyFourDR_1361
      · exact prime_oneHundredTwentyFourDR_274069
      · exact prime_oneHundredTwentyFourDR_630613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 126079869173764313) ^ 63039934586882156 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 126079869173764313) ^ 1881789092145736 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 126079869173764313) ^ 92637670223192 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 126079869173764313) ^ 460029661048 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 126079869173764313) ^ 199932239224 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_158229238067428459 : Nat.Prime 158229238067428459 := by
  apply lucas_primality 158229238067428459 (2 : ZMod 158229238067428459)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3767362811129249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3767362811129249, 1)] : List FactorBlock).map factorBlockValue).prod) = 158229238067428459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_3767362811129249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 158229238067428459) ^ 79114619033714229 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 158229238067428459) ^ 52743079355809486 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 158229238067428459) ^ 22604176866775494 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 158229238067428459) ^ 42 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_221300601157120559 : Nat.Prime 221300601157120559 := by
  apply lucas_primality 221300601157120559 (7 : ZMod 221300601157120559)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 1), (200817242429329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 1), (200817242429329, 1)] : List FactorBlock).map factorBlockValue).prod) = 221300601157120559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_29
      · exact prime_oneHundredTwentyFourDR_200817242429329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 221300601157120559) ^ 110650300578560279 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 221300601157120559) ^ 11647400060901082 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 221300601157120559) ^ 7631055212314502 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 221300601157120559) ^ 1102 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_297137927105221561 : Nat.Prime 297137927105221561 := by
  apply lucas_primality 297137927105221561 (17 : ZMod 297137927105221561)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (2476149392543513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (2476149392543513, 1)] : List FactorBlock).map factorBlockValue).prod) = 297137927105221561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_2476149392543513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 297137927105221561) ^ 148568963552610780 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 297137927105221561) ^ 99045975701740520 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 297137927105221561) ^ 59427585421044312 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (17 : ZMod 297137927105221561) ^ 120 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_367932905030454989 : Nat.Prime 367932905030454989 := by
  apply lucas_primality 367932905030454989 (2 : ZMod 367932905030454989)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (809, 1), (10861, 1), (14011, 1), (106739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (809, 1), (10861, 1), (14011, 1), (106739, 1)] : List FactorBlock).map factorBlockValue).prod) = 367932905030454989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_809
      · exact prime_oneHundredTwentyFourDR_10861
      · exact prime_oneHundredTwentyFourDR_14011
      · exact prime_oneHundredTwentyFourDR_106739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 367932905030454989) ^ 183966452515227494 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 367932905030454989) ^ 52561843575779284 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 367932905030454989) ^ 454799635389932 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 367932905030454989) ^ 33876521962108 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 367932905030454989) ^ 26260288703908 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 367932905030454989) ^ 3447033465092 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_610901771565687193 : Nat.Prime 610901771565687193 := by
  apply lucas_primality 610901771565687193 (5 : ZMod 610901771565687193)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (269, 1), (2887, 1), (3641820779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (269, 1), (2887, 1), (3641820779, 1)] : List FactorBlock).map factorBlockValue).prod) = 610901771565687193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_269
      · exact prime_oneHundredTwentyFourDR_2887
      · exact prime_oneHundredTwentyFourDR_3641820779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 610901771565687193) ^ 305450885782843596 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 610901771565687193) ^ 203633923855229064 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 610901771565687193) ^ 2271010303218168 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 610901771565687193) ^ 211604354543016 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 610901771565687193) ^ 167746248 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_683291315954695087 : Nat.Prime 683291315954695087 := by
  apply lucas_primality 683291315954695087 (3 : ZMod 683291315954695087)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (503, 1), (6637, 1), (199488901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (503, 1), (6637, 1), (199488901, 1)] : List FactorBlock).map factorBlockValue).prod) = 683291315954695087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_503
      · exact prime_oneHundredTwentyFourDR_6637
      · exact prime_oneHundredTwentyFourDR_199488901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 683291315954695087) ^ 341645657977347543 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 683291315954695087) ^ 227763771984898362 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 683291315954695087) ^ 35962700839720794 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 683291315954695087) ^ 1358432039671362 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 683291315954695087) ^ 102951833050278 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 683291315954695087) ^ 3425209686 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_709481005865533459 : Nat.Prime 709481005865533459 := by
  apply lucas_primality 709481005865533459 (2 : ZMod 709481005865533459)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (19, 1), (75083, 1), (3069944617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (19, 1), (75083, 1), (3069944617, 1)] : List FactorBlock).map factorBlockValue).prod) = 709481005865533459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_19
      · exact prime_oneHundredTwentyFourDR_75083
      · exact prime_oneHundredTwentyFourDR_3069944617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 709481005865533459) ^ 354740502932766729 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 709481005865533459) ^ 236493668621844486 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 709481005865533459) ^ 37341105571870182 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 709481005865533459) ^ 9449289531126 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 709481005865533459) ^ 231105474 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_727408625826681937 : Nat.Prime 727408625826681937 := by
  apply lucas_primality 727408625826681937 (5 : ZMod 727408625826681937)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (23, 1), (43, 1), (421, 1), (12132144301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (23, 1), (43, 1), (421, 1), (12132144301, 1)] : List FactorBlock).map factorBlockValue).prod) = 727408625826681937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_43
      · exact prime_oneHundredTwentyFourDR_421
      · exact prime_oneHundredTwentyFourDR_12132144301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 727408625826681937) ^ 363704312913340968 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 242469541942227312 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 31626461992464432 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 16916479670387952 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 1727811462771216 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 59957136 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_783404528361724747 : Nat.Prime 783404528361724747 := by
  apply lucas_primality 783404528361724747 (2 : ZMod 783404528361724747)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (239, 1), (367, 1), (377557, 1), (1314217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (239, 1), (367, 1), (377557, 1), (1314217, 1)] : List FactorBlock).map factorBlockValue).prod) = 783404528361724747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_239
      · exact prime_oneHundredTwentyFourDR_367
      · exact prime_oneHundredTwentyFourDR_377557
      · exact prime_oneHundredTwentyFourDR_1314217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 783404528361724747) ^ 391702264180862373 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 783404528361724747) ^ 261134842787241582 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 783404528361724747) ^ 3277843214902614 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 783404528361724747) ^ 2134617243492438 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 783404528361724747) ^ 2074930482978 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 783404528361724747) ^ 596099828538 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1105568479646925799 : Nat.Prime 1105568479646925799 := by
  apply lucas_primality 1105568479646925799 (7 : ZMod 1105568479646925799)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (617, 1), (42662980614607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (617, 1), (42662980614607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1105568479646925799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_617
      · exact prime_oneHundredTwentyFourDR_42662980614607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1105568479646925799) ^ 552784239823462899 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1105568479646925799) ^ 368522826548975266 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1105568479646925799) ^ 157938354235275114 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1105568479646925799) ^ 1791845185813494 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1105568479646925799) ^ 25914 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1391716646373735443 : Nat.Prime 1391716646373735443 := by
  apply lucas_primality 1391716646373735443 (2 : ZMod 1391716646373735443)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (1425877, 1), (1724456831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (1425877, 1), (1724456831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1391716646373735443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_283
      · exact prime_oneHundredTwentyFourDR_1425877
      · exact prime_oneHundredTwentyFourDR_1724456831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1391716646373735443) ^ 695858323186867721 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1391716646373735443) ^ 4917726665631574 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1391716646373735443) ^ 976042566346 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1391716646373735443) ^ 807046382 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2211988974136255507 : Nat.Prime 2211988974136255507 := by
  apply lucas_primality 2211988974136255507 (2 : ZMod 2211988974136255507)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (4409, 1), (109721, 1), (10439483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (4409, 1), (109721, 1), (10439483, 1)] : List FactorBlock).map factorBlockValue).prod) = 2211988974136255507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_73
      · exact prime_oneHundredTwentyFourDR_4409
      · exact prime_oneHundredTwentyFourDR_109721
      · exact prime_oneHundredTwentyFourDR_10439483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2211988974136255507) ^ 1105994487068127753 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211988974136255507) ^ 737329658045418502 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211988974136255507) ^ 30301218823784322 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211988974136255507) ^ 501698565238434 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211988974136255507) ^ 20160124079586 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2211988974136255507) ^ 211886831382 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_101
      · exact prime_oneHundredTwentyFourDR_191
      · exact prime_oneHundredTwentyFourDR_48017
      · exact prime_oneHundredTwentyFourDR_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2901461851911455687 : Nat.Prime 2901461851911455687 := by
  apply lucas_primality 2901461851911455687 (5 : ZMod 2901461851911455687)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (167, 1), (439, 1), (3049, 1), (927150877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (167, 1), (439, 1), (3049, 1), (927150877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2901461851911455687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_167
      · exact prime_oneHundredTwentyFourDR_439
      · exact prime_oneHundredTwentyFourDR_3049
      · exact prime_oneHundredTwentyFourDR_927150877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2901461851911455687) ^ 1450730925955727843 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 414494550273065098 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 17374023065338058 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 6609252510048874 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 951610971437014 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 3129438718 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_3907541947548230501 : Nat.Prime 3907541947548230501 := by
  apply lucas_primality 3907541947548230501 (2 : ZMod 3907541947548230501)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (9029, 1), (865553648809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (9029, 1), (865553648809, 1)] : List FactorBlock).map factorBlockValue).prod) = 3907541947548230501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_9029
      · exact prime_oneHundredTwentyFourDR_865553648809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3907541947548230501) ^ 1953770973774115250 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3907541947548230501) ^ 781508389509646100 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3907541947548230501) ^ 432776824404500 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3907541947548230501) ^ 4514500 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_4382602193503262191 : Nat.Prime 4382602193503262191 := by
  apply lucas_primality 4382602193503262191 (3 : ZMod 4382602193503262191)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (253871, 1), (1067600917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (253871, 1), (1067600917, 1)] : List FactorBlock).map factorBlockValue).prod) = 4382602193503262191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_253871
      · exact prime_oneHundredTwentyFourDR_1067600917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4382602193503262191) ^ 2191301096751631095 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 1460867397834420730 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 876520438700652438 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 626086027643323170 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 398418381227569290 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 17263106827890 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 4105094070 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_6331721060848760953 : Nat.Prime 6331721060848760953 := by
  apply lucas_primality 6331721060848760953 (5 : ZMod 6331721060848760953)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (641, 1), (411578332088453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (641, 1), (411578332088453, 1)] : List FactorBlock).map factorBlockValue).prod) = 6331721060848760953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_641
      · exact prime_oneHundredTwentyFourDR_411578332088453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6331721060848760953) ^ 3165860530424380476 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6331721060848760953) ^ 2110573686949586984 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6331721060848760953) ^ 9877879970122872 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 6331721060848760953) ^ 15384 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_7596680508025691879 : Nat.Prime 7596680508025691879 := by
  apply lucas_primality 7596680508025691879 (11 : ZMod 7596680508025691879)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (64067, 1), (3487470611201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (64067, 1), (3487470611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 7596680508025691879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_64067
      · exact prime_oneHundredTwentyFourDR_3487470611201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7596680508025691879) ^ 3798340254012845939 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 7596680508025691879) ^ 446863559295628934 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 7596680508025691879) ^ 118574000780834 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 7596680508025691879) ^ 2178278 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_9109210463193999337 : Nat.Prime 9109210463193999337 := by
  apply lucas_primality 9109210463193999337 (10 : ZMod 9109210463193999337)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (12243562450529569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (12243562450529569, 1)] : List FactorBlock).map factorBlockValue).prod) = 9109210463193999337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_12243562450529569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 9109210463193999337) ^ 4554605231596999668 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 9109210463193999337) ^ 3036403487731333112 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 9109210463193999337) ^ 293845498812709656 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 9109210463193999337) ^ 744 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_9154757522977371733 : Nat.Prime 9154757522977371733 := by
  apply lucas_primality 9154757522977371733 (5 : ZMod 9154757522977371733)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (47, 1), (9833, 1), (33688806289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (47, 1), (9833, 1), (33688806289, 1)] : List FactorBlock).map factorBlockValue).prod) = 9154757522977371733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_47
      · exact prime_oneHundredTwentyFourDR_9833
      · exact prime_oneHundredTwentyFourDR_33688806289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9154757522977371733) ^ 4577378761488685866 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9154757522977371733) ^ 3051585840992457244 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9154757522977371733) ^ 1307822503282481676 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9154757522977371733) ^ 194782074956965356 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9154757522977371733) ^ 931023850602804 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9154757522977371733) ^ 271744788 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_21506763405413311873 : Nat.Prime 21506763405413311873 := by
  apply lucas_primality 21506763405413311873 (19 : ZMod 21506763405413311873)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (11, 1), (17, 1), (1193, 1), (35864414309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (11, 1), (17, 1), (1193, 1), (35864414309, 1)] : List FactorBlock).map factorBlockValue).prod) = 21506763405413311873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_1193
      · exact prime_oneHundredTwentyFourDR_35864414309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 21506763405413311873) ^ 10753381702706655936 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 7168921135137770624 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 3072394772201901696 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 1955160309583028352 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 1265103729730194816 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 18027463038904704 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 599668608 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_36485573859983357449 : Nat.Prime 36485573859983357449 := by
  apply lucas_primality 36485573859983357449 (11 : ZMod 36485573859983357449)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (16381, 1), (4034982851729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (16381, 1), (4034982851729, 1)] : List FactorBlock).map factorBlockValue).prod) = 36485573859983357449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_16381
      · exact prime_oneHundredTwentyFourDR_4034982851729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 36485573859983357449) ^ 18242786929991678724 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36485573859983357449) ^ 12161857953327785816 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36485573859983357449) ^ 1586329298260145976 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36485573859983357449) ^ 2227310534154408 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36485573859983357449) ^ 9042312 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_38820817028098341449 : Nat.Prime 38820817028098341449 := by
  apply lucas_primality 38820817028098341449 (3 : ZMod 38820817028098341449)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (101, 1), (21997, 1), (59032086229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (101, 1), (21997, 1), (59032086229, 1)] : List FactorBlock).map factorBlockValue).prod) = 38820817028098341449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_101
      · exact prime_oneHundredTwentyFourDR_21997
      · exact prime_oneHundredTwentyFourDR_59032086229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38820817028098341449) ^ 19410408514049170724 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38820817028098341449) ^ 1049211271029684904 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38820817028098341449) ^ 384364525030676648 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38820817028098341449) ^ 1764823249902184 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38820817028098341449) ^ 657622312 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_43237126432462330213 : Nat.Prime 43237126432462330213 := by
  apply lucas_primality 43237126432462330213 (2 : ZMod 43237126432462330213)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (109, 1), (480569, 1), (5291148787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (109, 1), (480569, 1), (5291148787, 1)] : List FactorBlock).map factorBlockValue).prod) = 43237126432462330213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_109
      · exact prime_oneHundredTwentyFourDR_480569
      · exact prime_oneHundredTwentyFourDR_5291148787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43237126432462330213) ^ 21618563216231165106 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43237126432462330213) ^ 14412375477487443404 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43237126432462330213) ^ 3325932802497102324 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43237126432462330213) ^ 396670884701489268 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43237126432462330213) ^ 89970693974148 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43237126432462330213) ^ 8171595276 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_232034846519226569447 : Nat.Prime 232034846519226569447 := by
  apply lucas_primality 232034846519226569447 (5 : ZMod 232034846519226569447)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (196429, 1), (590632866122687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (196429, 1), (590632866122687, 1)] : List FactorBlock).map factorBlockValue).prod) = 232034846519226569447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_196429
      · exact prime_oneHundredTwentyFourDR_590632866122687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 232034846519226569447) ^ 116017423259613284723 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 232034846519226569447) ^ 1181265732245374 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 232034846519226569447) ^ 392858 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_313357880006437214197 : Nat.Prime 313357880006437214197 := by
  apply lucas_primality 313357880006437214197 (2 : ZMod 313357880006437214197)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (2901461851911455687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (2901461851911455687, 1)] : List FactorBlock).map factorBlockValue).prod) = 313357880006437214197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_2901461851911455687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 313357880006437214197) ^ 156678940003218607098 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 313357880006437214197) ^ 104452626668812404732 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 313357880006437214197) ^ 108 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_423718684052045945987 : Nat.Prime 423718684052045945987 := by
  apply lucas_primality 423718684052045945987 (2 : ZMod 423718684052045945987)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (31, 1), (297137927105221561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (31, 1), (297137927105221561, 1)] : List FactorBlock).map factorBlockValue).prod) = 423718684052045945987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_297137927105221561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 423718684052045945987) ^ 211859342026022972993 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 423718684052045945987) ^ 18422551480523736782 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 423718684052045945987) ^ 13668344646840191806 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 423718684052045945987) ^ 1426 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_944162800047756383621 : Nat.Prime 944162800047756383621 := by
  apply lucas_primality 944162800047756383621 (2 : ZMod 944162800047756383621)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (881, 1), (1129, 1), (2063569989203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (881, 1), (1129, 1), (2063569989203, 1)] : List FactorBlock).map factorBlockValue).prod) = 944162800047756383621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_881
      · exact prime_oneHundredTwentyFourDR_1129
      · exact prime_oneHundredTwentyFourDR_2063569989203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 944162800047756383621) ^ 472081400023878191810 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 944162800047756383621) ^ 188832560009551276724 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 944162800047756383621) ^ 41050556523815494940 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 944162800047756383621) ^ 1071694438192686020 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 944162800047756383621) ^ 836282373824407780 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 944162800047756383621) ^ 457538540 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_955177357414373605007 : Nat.Prime 955177357414373605007 := by
  apply lucas_primality 955177357414373605007 (5 : ZMod 955177357414373605007)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (509, 1), (7204189, 1), (11840184173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (509, 1), (7204189, 1), (11840184173, 1)] : List FactorBlock).map factorBlockValue).prod) = 955177357414373605007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_509
      · exact prime_oneHundredTwentyFourDR_7204189
      · exact prime_oneHundredTwentyFourDR_11840184173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 955177357414373605007) ^ 477588678707186802503 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 955177357414373605007) ^ 86834305219488509546 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 955177357414373605007) ^ 1876576340696215334 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 955177357414373605007) ^ 132586382369254 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 955177357414373605007) ^ 80672508422 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_996345374177602247033 : Nat.Prime 996345374177602247033 := by
  apply lucas_primality 996345374177602247033 (3 : ZMod 996345374177602247033)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (317, 1), (977, 1), (1193, 1), (25928792959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (317, 1), (977, 1), (1193, 1), (25928792959, 1)] : List FactorBlock).map factorBlockValue).prod) = 996345374177602247033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_317
      · exact prime_oneHundredTwentyFourDR_977
      · exact prime_oneHundredTwentyFourDR_1193
      · exact prime_oneHundredTwentyFourDR_25928792959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 996345374177602247033) ^ 498172687088801123516 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 996345374177602247033) ^ 76641951859815557464 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 996345374177602247033) ^ 3143045344408839896 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 996345374177602247033) ^ 1019800792402868216 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 996345374177602247033) ^ 835159576008048824 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 996345374177602247033) ^ 38426215048 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1354661562452864814881 : Nat.Prime 1354661562452864814881 := by
  apply lucas_primality 1354661562452864814881 (3 : ZMod 1354661562452864814881)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (37, 1), (41, 1), (5581169917818329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (37, 1), (41, 1), (5581169917818329, 1)] : List FactorBlock).map factorBlockValue).prod) = 1354661562452864814881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_41
      · exact prime_oneHundredTwentyFourDR_5581169917818329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1354661562452864814881) ^ 677330781226432407440 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1354661562452864814881) ^ 270932312490572962976 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1354661562452864814881) ^ 36612474660888238240 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1354661562452864814881) ^ 33040525913484507680 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1354661562452864814881) ^ 242720 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1513224681261365355221 : Nat.Prime 1513224681261365355221 := by
  apply lucas_primality 1513224681261365355221 (2 : ZMod 1513224681261365355221)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (526193, 1), (20541412985911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (526193, 1), (20541412985911, 1)] : List FactorBlock).map factorBlockValue).prod) = 1513224681261365355221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_526193
      · exact prime_oneHundredTwentyFourDR_20541412985911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1513224681261365355221) ^ 756612340630682677610 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1513224681261365355221) ^ 302644936252273071044 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1513224681261365355221) ^ 216174954465909336460 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1513224681261365355221) ^ 2875797818027540 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1513224681261365355221) ^ 73667020 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1976673880107317503279 : Nat.Prime 1976673880107317503279 := by
  apply lucas_primality 1976673880107317503279 (6 : ZMod 1976673880107317503279)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (13613, 1), (474525715304651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (13613, 1), (474525715304651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1976673880107317503279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_13613
      · exact prime_oneHundredTwentyFourDR_474525715304651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1976673880107317503279) ^ 988336940053658751639 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1976673880107317503279) ^ 658891293369105834426 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1976673880107317503279) ^ 116274934123959853134 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1976673880107317503279) ^ 145204868883223206 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (6 : ZMod 1976673880107317503279) ^ 4165578 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2740309081917507835177 : Nat.Prime 2740309081917507835177 := by
  apply lucas_primality 2740309081917507835177 (5 : ZMod 2740309081917507835177)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (61, 1), (1715927, 1), (83910500809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (61, 1), (1715927, 1), (83910500809, 1)] : List FactorBlock).map factorBlockValue).prod) = 2740309081917507835177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_61
      · exact prime_oneHundredTwentyFourDR_1715927
      · exact prime_oneHundredTwentyFourDR_83910500809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2740309081917507835177) ^ 1370154540958753917588 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740309081917507835177) ^ 913436360639169278392 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740309081917507835177) ^ 210793006301346756552 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740309081917507835177) ^ 44923099703565702216 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740309081917507835177) ^ 1596984651396888 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2740309081917507835177) ^ 32657522664 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_4120462932770454404731 : Nat.Prime 4120462932770454404731 := by
  apply lucas_primality 4120462932770454404731 (10 : ZMod 4120462932770454404731)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (11462203, 1), (178847081891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (11462203, 1), (178847081891, 1)] : List FactorBlock).map factorBlockValue).prod) = 4120462932770454404731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_67
      · exact prime_oneHundredTwentyFourDR_11462203
      · exact prime_oneHundredTwentyFourDR_178847081891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4120462932770454404731) ^ 2060231466385227202365 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 1373487644256818134910 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 824092586554090880946 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 61499446757767976190 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 359482634600910 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 23039028030 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_8080279103145866249417 : Nat.Prime 8080279103145866249417 := by
  apply lucas_primality 8080279103145866249417 (3 : ZMod 8080279103145866249417)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (37, 1), (503, 1), (1109, 1), (6990964227089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (37, 1), (503, 1), (1109, 1), (6990964227089, 1)] : List FactorBlock).map factorBlockValue).prod) = 8080279103145866249417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_503
      · exact prime_oneHundredTwentyFourDR_1109
      · exact prime_oneHundredTwentyFourDR_6990964227089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8080279103145866249417) ^ 4040139551572933124708 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8080279103145866249417) ^ 1154325586163695178488 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8080279103145866249417) ^ 218385921706645033768 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8080279103145866249417) ^ 16064173167288004472 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8080279103145866249417) ^ 7286094772899789224 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8080279103145866249417) ^ 1155817544 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_12904058043247987123801 : Nat.Prime 12904058043247987123801 := by
  apply lucas_primality 12904058043247987123801 (11 : ZMod 12904058043247987123801)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (21506763405413311873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (21506763405413311873, 1)] : List FactorBlock).map factorBlockValue).prod) = 12904058043247987123801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_21506763405413311873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 12904058043247987123801) ^ 6452029021623993561900 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 12904058043247987123801) ^ 4301352681082662374600 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 12904058043247987123801) ^ 2580811608649597424760 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 12904058043247987123801) ^ 600 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_16012976927695174287437 : Nat.Prime 16012976927695174287437 := by
  apply lucas_primality 16012976927695174287437 (2 : ZMod 16012976927695174287437)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (59077, 1), (670922381031467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (59077, 1), (670922381031467, 1)] : List FactorBlock).map factorBlockValue).prod) = 16012976927695174287437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_101
      · exact prime_oneHundredTwentyFourDR_59077
      · exact prime_oneHundredTwentyFourDR_670922381031467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16012976927695174287437) ^ 8006488463847587143718 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16012976927695174287437) ^ 158544326016783903836 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16012976927695174287437) ^ 271052641936712668 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16012976927695174287437) ^ 23867108 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_22951075064915360481269 : Nat.Prime 22951075064915360481269 := by
  apply lucas_primality 22951075064915360481269 (2 : ZMod 22951075064915360481269)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (2677, 1), (126079869173764313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (2677, 1), (126079869173764313, 1)] : List FactorBlock).map factorBlockValue).prod) = 22951075064915360481269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_17
      · exact prime_oneHundredTwentyFourDR_2677
      · exact prime_oneHundredTwentyFourDR_126079869173764313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22951075064915360481269) ^ 11475537532457680240634 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951075064915360481269) ^ 1350063239112668263604 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951075064915360481269) ^ 8573431103815973284 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951075064915360481269) ^ 182036 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_31355182619851400003039 : Nat.Prime 31355182619851400003039 := by
  apply lucas_primality 31355182619851400003039 (11 : ZMod 31355182619851400003039)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (423718684052045945987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (423718684052045945987, 1)] : List FactorBlock).map factorBlockValue).prod) = 31355182619851400003039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_423718684052045945987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 31355182619851400003039) ^ 15677591309925700001519 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 31355182619851400003039) ^ 847437368104091891974 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 31355182619851400003039) ^ 74 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_45963847361268436275617 : Nat.Prime 45963847361268436275617 := by
  apply lucas_primality 45963847361268436275617 (3 : ZMod 45963847361268436275617)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (38820817028098341449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (38820817028098341449, 1)] : List FactorBlock).map factorBlockValue).prod) = 45963847361268436275617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_37
      · exact prime_oneHundredTwentyFourDR_38820817028098341449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 45963847361268436275617) ^ 22981923680634218137808 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45963847361268436275617) ^ 1242266144899146926368 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45963847361268436275617) ^ 1184 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_110996938618810116403127 : Nat.Prime 110996938618810116403127 := by
  apply lucas_primality 110996938618810116403127 (5 : ZMod 110996938618810116403127)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (372059, 1), (1888174374868783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (372059, 1), (1888174374868783, 1)] : List FactorBlock).map factorBlockValue).prod) = 110996938618810116403127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_79
      · exact prime_oneHundredTwentyFourDR_372059
      · exact prime_oneHundredTwentyFourDR_1888174374868783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 110996938618810116403127) ^ 55498469309405058201563 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 110996938618810116403127) ^ 1405024539478609068394 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 110996938618810116403127) ^ 298331551229267714 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 110996938618810116403127) ^ 58785322 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_111936831469705874816011 : Nat.Prime 111936831469705874816011 := by
  apply lucas_primality 111936831469705874816011 (2 : ZMod 111936831469705874816011)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (47, 1), (61, 1), (263, 1), (4357, 1), (126193865579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (47, 1), (61, 1), (263, 1), (4357, 1), (126193865579, 1)] : List FactorBlock).map factorBlockValue).prod) = 111936831469705874816011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_47
      · exact prime_oneHundredTwentyFourDR_61
      · exact prime_oneHundredTwentyFourDR_263
      · exact prime_oneHundredTwentyFourDR_4357
      · exact prime_oneHundredTwentyFourDR_126193865579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 111936831469705874816011) ^ 55968415734852937408005 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 111936831469705874816011) ^ 37312277156568624938670 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 111936831469705874816011) ^ 22387366293941174963202 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 111936831469705874816011) ^ 2381634712121401591830 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 111936831469705874816011) ^ 1835030024093538931410 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 111936831469705874816011) ^ 425615328782151615270 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 111936831469705874816011) ^ 25691262673790652930 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 111936831469705874816011) ^ 887022764190 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_189541294907440902617627 : Nat.Prime 189541294907440902617627 := by
  apply lucas_primality 189541294907440902617627 (2 : ZMod 189541294907440902617627)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (4120462932770454404731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (4120462932770454404731, 1)] : List FactorBlock).map factorBlockValue).prod) = 189541294907440902617627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_4120462932770454404731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 189541294907440902617627) ^ 94770647453720451308813 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 189541294907440902617627) ^ 8240925865540908809462 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 189541294907440902617627) ^ 46 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_330277114464610330007477 : Nat.Prime 330277114464610330007477 := by
  apply lucas_primality 330277114464610330007477 (2 : ZMod 330277114464610330007477)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (88238207, 1), (935754265906067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (88238207, 1), (935754265906067, 1)] : List FactorBlock).map factorBlockValue).prod) = 330277114464610330007477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_88238207
      · exact prime_oneHundredTwentyFourDR_935754265906067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 330277114464610330007477) ^ 165138557232305165003738 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 330277114464610330007477) ^ 3743017063624268 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 330277114464610330007477) ^ 352952828 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_524063836750506654457937 : Nat.Prime 524063836750506654457937 := by
  apply lucas_primality 524063836750506654457937 (3 : ZMod 524063836750506654457937)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (395429, 1), (422407, 1), (196094126807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (395429, 1), (422407, 1), (196094126807, 1)] : List FactorBlock).map factorBlockValue).prod) = 524063836750506654457937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_395429
      · exact prime_oneHundredTwentyFourDR_422407
      · exact prime_oneHundredTwentyFourDR_196094126807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 524063836750506654457937) ^ 262031918375253327228968 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 524063836750506654457937) ^ 1325304509154631184 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 524063836750506654457937) ^ 1240660871506643248 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 524063836750506654457937) ^ 2672511641648 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_6212700497044114972725721 : Nat.Prime 6212700497044114972725721 := by
  apply lucas_primality 6212700497044114972725721 (7 : ZMod 6212700497044114972725721)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (31, 1), (263, 1), (9923, 1), (639939235066399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (31, 1), (263, 1), (9923, 1), (639939235066399, 1)] : List FactorBlock).map factorBlockValue).prod) = 6212700497044114972725721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_263
      · exact prime_oneHundredTwentyFourDR_9923
      · exact prime_oneHundredTwentyFourDR_639939235066399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6212700497044114972725721) ^ 3106350248522057486362860 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 6212700497044114972725721) ^ 2070900165681371657575240 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 6212700497044114972725721) ^ 1242540099408822994545144 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 6212700497044114972725721) ^ 200409693453035966862120 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 6212700497044114972725721) ^ 23622435349977623470440 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 6212700497044114972725721) ^ 626090950019562125640 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (7 : ZMod 6212700497044114972725721) ^ 9708266280 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_7448107180244372352355273 : Nat.Prime 7448107180244372352355273 := by
  apply lucas_primality 7448107180244372352355273 (5 : ZMod 7448107180244372352355273)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (157, 1), (1976673880107317503279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (157, 1), (1976673880107317503279, 1)] : List FactorBlock).map factorBlockValue).prod) = 7448107180244372352355273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_157
      · exact prime_oneHundredTwentyFourDR_1976673880107317503279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7448107180244372352355273) ^ 3724053590122186176177636 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7448107180244372352355273) ^ 2482702393414790784118424 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7448107180244372352355273) ^ 47440173122575620078696 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7448107180244372352355273) ^ 3768 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_7891537580273993702503571 : Nat.Prime 7891537580273993702503571 := by
  apply lucas_primality 7891537580273993702503571 (2 : ZMod 7891537580273993702503571)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5477, 1), (7547, 1), (17393, 1), (1097665567571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5477, 1), (7547, 1), (17393, 1), (1097665567571, 1)] : List FactorBlock).map factorBlockValue).prod) = 7891537580273993702503571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_5477
      · exact prime_oneHundredTwentyFourDR_7547
      · exact prime_oneHundredTwentyFourDR_17393
      · exact prime_oneHundredTwentyFourDR_1097665567571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7891537580273993702503571) ^ 3945768790136996851251785 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7891537580273993702503571) ^ 1578307516054798740500714 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7891537580273993702503571) ^ 1440850388949058554410 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7891537580273993702503571) ^ 1045652256562076812310 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7891537580273993702503571) ^ 453719173246363117490 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7891537580273993702503571) ^ 7189382461670 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_20455015156795030139724967 : Nat.Prime 20455015156795030139724967 := by
  apply lucas_primality 20455015156795030139724967 (3 : ZMod 20455015156795030139724967)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (1429, 1), (39548843, 1), (597256891963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (1429, 1), (39548843, 1), (597256891963, 1)] : List FactorBlock).map factorBlockValue).prod) = 20455015156795030139724967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_101
      · exact prime_oneHundredTwentyFourDR_1429
      · exact prime_oneHundredTwentyFourDR_39548843
      · exact prime_oneHundredTwentyFourDR_597256891963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20455015156795030139724967) ^ 10227507578397515069862483 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20455015156795030139724967) ^ 6818338385598343379908322 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20455015156795030139724967) ^ 202524902542525050888366 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20455015156795030139724967) ^ 14314216344853065178254 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20455015156795030139724967) ^ 517208939760766962 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20455015156795030139724967) ^ 34248269768082 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_44170260207517318774151503 : Nat.Prime 44170260207517318774151503 := by
  apply lucas_primality 44170260207517318774151503 (3 : ZMod 44170260207517318774151503)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (29, 1), (57999273037, 1), (162104247727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (29, 1), (57999273037, 1), (162104247727, 1)] : List FactorBlock).map factorBlockValue).prod) = 44170260207517318774151503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_29
      · exact prime_oneHundredTwentyFourDR_57999273037
      · exact prime_oneHundredTwentyFourDR_162104247727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44170260207517318774151503) ^ 22085130103758659387075751 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 44170260207517318774151503) ^ 14723420069172439591383834 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 44170260207517318774151503) ^ 1523112420948873061177638 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 44170260207517318774151503) ^ 761565755821446 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 44170260207517318774151503) ^ 272480584727826 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_108033230382277067805017567 : Nat.Prime 108033230382277067805017567 := by
  apply lucas_primality 108033230382277067805017567 (5 : ZMod 108033230382277067805017567)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (181513, 1), (6331721060848760953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (181513, 1), (6331721060848760953, 1)] : List FactorBlock).map factorBlockValue).prod) = 108033230382277067805017567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_47
      · exact prime_oneHundredTwentyFourDR_181513
      · exact prime_oneHundredTwentyFourDR_6331721060848760953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 108033230382277067805017567) ^ 54016615191138533902508783 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 108033230382277067805017567) ^ 2298579369835682293723778 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 108033230382277067805017567) ^ 595181779719783529582 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 108033230382277067805017567) ^ 17062222 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_314594621520922706033066177 : Nat.Prime 314594621520922706033066177 := by
  apply lucas_primality 314594621520922706033066177 (3 : ZMod 314594621520922706033066177)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (109, 1), (120243971, 1), (375043386305381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (109, 1), (120243971, 1), (375043386305381, 1)] : List FactorBlock).map factorBlockValue).prod) = 314594621520922706033066177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_109
      · exact prime_oneHundredTwentyFourDR_120243971
      · exact prime_oneHundredTwentyFourDR_375043386305381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 314594621520922706033066177) ^ 157297310760461353016533088 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 314594621520922706033066177) ^ 2886189188265345926908864 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 314594621520922706033066177) ^ 2616302662866337856 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 314594621520922706033066177) ^ 838821941696 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_1211579286188016371995114367 : Nat.Prime 1211579286188016371995114367 := by
  apply lucas_primality 1211579286188016371995114367 (5 : ZMod 1211579286188016371995114367)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1151603, 1), (433055573, 1), (1214717881457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1151603, 1), (433055573, 1), (1214717881457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1211579286188016371995114367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_1151603
      · exact prime_oneHundredTwentyFourDR_433055573
      · exact prime_oneHundredTwentyFourDR_1214717881457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1211579286188016371995114367) ^ 605789643094008185997557183 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1211579286188016371995114367) ^ 1052080696375414419722 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1211579286188016371995114367) ^ 2797745512879051142 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1211579286188016371995114367) ^ 997416194067038 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_2290642087949218453303263101 : Nat.Prime 2290642087949218453303263101 := by
  apply lucas_primality 2290642087949218453303263101 (2 : ZMod 2290642087949218453303263101)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2290642087949218453303263101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_171401
      · exact prime_oneHundredTwentyFourDR_714027719
      · exact prime_oneHundredTwentyFourDR_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2290642087949218453303263101) ^ 1145321043974609226651631550 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 458128417589843690660652620 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 73891680256426401719460100 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 13364228259748883923100 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 3208057652379764900 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 379393701699388900 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_7715847033092104263758359921 : Nat.Prime 7715847033092104263758359921 := by
  apply lucas_primality 7715847033092104263758359921 (11 : ZMod 7715847033092104263758359921)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (15629399, 1), (158229238067428459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (15629399, 1), (158229238067428459, 1)] : List FactorBlock).map factorBlockValue).prod) = 7715847033092104263758359921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_15629399
      · exact prime_oneHundredTwentyFourDR_158229238067428459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7715847033092104263758359921) ^ 3857923516546052131879179960 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 7715847033092104263758359921) ^ 2571949011030701421252786640 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 7715847033092104263758359921) ^ 1543169406618420852751671984 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 7715847033092104263758359921) ^ 593526694853238789519873840 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 7715847033092104263758359921) ^ 493675222770376792080 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 7715847033092104263758359921) ^ 48763724880 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_8144505201597221167300491023 : Nat.Prime 8144505201597221167300491023 := by
  apply lucas_primality 8144505201597221167300491023 (5 : ZMod 8144505201597221167300491023)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (1087, 1), (13809643, 1), (1072265153536007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (1087, 1), (13809643, 1), (1072265153536007, 1)] : List FactorBlock).map factorBlockValue).prod) = 8144505201597221167300491023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_23
      · exact prime_oneHundredTwentyFourDR_1087
      · exact prime_oneHundredTwentyFourDR_13809643
      · exact prime_oneHundredTwentyFourDR_1072265153536007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8144505201597221167300491023) ^ 4072252600798610583650245511 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8144505201597221167300491023) ^ 740409563781565560663681002 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8144505201597221167300491023) ^ 354108921808574833360890914 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8144505201597221167300491023) ^ 7492645079666256823643506 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8144505201597221167300491023) ^ 589769424278181642154 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8144505201597221167300491023) ^ 7595607462146 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_18325136703593747626426104803 : Nat.Prime 18325136703593747626426104803 := by
  apply lucas_primality 18325136703593747626426104803 (2 : ZMod 18325136703593747626426104803)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (353, 1), (431, 1), (106747, 1), (11513662460653469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (353, 1), (431, 1), (106747, 1), (11513662460653469, 1)] : List FactorBlock).map factorBlockValue).prod) = 18325136703593747626426104803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_353
      · exact prime_oneHundredTwentyFourDR_431
      · exact prime_oneHundredTwentyFourDR_106747
      · exact prime_oneHundredTwentyFourDR_11513662460653469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18325136703593747626426104803) ^ 9162568351796873813213052401 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 2617876671941963946632300686 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 51912568565421381377977634 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 42517718569823080339735742 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 171668868479617671938566 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 1591599264458 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_24433515604791663501901473073 : Nat.Prime 24433515604791663501901473073 := by
  apply lucas_primality 24433515604791663501901473073 (13 : ZMod 24433515604791663501901473073)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (193, 1), (1021, 1), (8184194567, 1), (105211804913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (193, 1), (1021, 1), (8184194567, 1), (105211804913, 1)] : List FactorBlock).map factorBlockValue).prod) = 24433515604791663501901473073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_193
      · exact prime_oneHundredTwentyFourDR_1021
      · exact prime_oneHundredTwentyFourDR_8184194567
      · exact prime_oneHundredTwentyFourDR_105211804913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 24433515604791663501901473073) ^ 12216757802395831750950736536 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791663501901473073) ^ 8144505201597221167300491024 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791663501901473073) ^ 126598526449697738351821104 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791663501901473073) ^ 23930965332802804605192432 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791663501901473073) ^ 2985451458267080016 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (13 : ZMod 24433515604791663501901473073) ^ 232231693249591344 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_29320218725749996202281767691 : Nat.Prime 29320218725749996202281767691 := by
  apply lucas_primality 29320218725749996202281767691 (2 : ZMod 29320218725749996202281767691)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (234659, 1), (583153, 1), (2380701615042083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (234659, 1), (583153, 1), (2380701615042083, 1)] : List FactorBlock).map factorBlockValue).prod) = 29320218725749996202281767691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_5
      · exact prime_oneHundredTwentyFourDR_234659
      · exact prime_oneHundredTwentyFourDR_583153
      · exact prime_oneHundredTwentyFourDR_2380701615042083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29320218725749996202281767691) ^ 14660109362874998101140883845 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 29320218725749996202281767691) ^ 9773406241916665400760589230 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 29320218725749996202281767691) ^ 5864043745149999240456353538 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 29320218725749996202281767691) ^ 124948196002497224492910 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 29320218725749996202281767691) ^ 50278775425574413922730 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 29320218725749996202281767691) ^ 12315788984430 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_36650273407187495252852209609 : Nat.Prime 36650273407187495252852209609 := by
  apply lucas_primality 36650273407187495252852209609 (11 : ZMod 36650273407187495252852209609)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (193, 1), (1021, 1), (8184194567, 1), (105211804913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (193, 1), (1021, 1), (8184194567, 1), (105211804913, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187495252852209609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_193
      · exact prime_oneHundredTwentyFourDR_1021
      · exact prime_oneHundredTwentyFourDR_8184194567
      · exact prime_oneHundredTwentyFourDR_105211804913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 36650273407187495252852209609) ^ 18325136703593747626426104804 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 12216757802395831750950736536 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 189897789674546607527731656 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 35896447999204206907788648 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 4478177187400620024 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 348347539874387016 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_48867031209583327003802946157 : Nat.Prime 48867031209583327003802946157 := by
  apply lucas_primality 48867031209583327003802946157 (2 : ZMod 48867031209583327003802946157)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (131, 1), (199, 1), (20563, 1), (7596680508025691879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (131, 1), (199, 1), (20563, 1), (7596680508025691879, 1)] : List FactorBlock).map factorBlockValue).prod) = 48867031209583327003802946157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_131
      · exact prime_oneHundredTwentyFourDR_199
      · exact prime_oneHundredTwentyFourDR_20563
      · exact prime_oneHundredTwentyFourDR_7596680508025691879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48867031209583327003802946157) ^ 24433515604791663501901473078 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 48867031209583327003802946157) ^ 16289010403194442334600982052 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 48867031209583327003802946157) ^ 373030772592239137433610276 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 48867031209583327003802946157) ^ 245562970902428778913582644 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 48867031209583327003802946157) ^ 2376454369964661139123812 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 48867031209583327003802946157) ^ 6432682164 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_146601093628749981011408838403 : Nat.Prime 146601093628749981011408838403 := by
  apply lucas_primality 146601093628749981011408838403 (5 : ZMod 146601093628749981011408838403)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (883, 1), (13909117, 1), (21861718784556967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (883, 1), (13909117, 1), (21861718784556967, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_7
      · exact prime_oneHundredTwentyFourDR_13
      · exact prime_oneHundredTwentyFourDR_883
      · exact prime_oneHundredTwentyFourDR_13909117
      · exact prime_oneHundredTwentyFourDR_21861718784556967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 146601093628749981011408838403) ^ 73300546814374990505704419201 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838403) ^ 48867031209583327003802946134 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838403) ^ 20943013375535711573058405486 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838403) ^ 11277007202211537000877602954 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838403) ^ 166026153599943353353803894 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838403) ^ 10539928136973035816106 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838403) ^ 6705835669806 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_146601093628749981011408838413 : Nat.Prime 146601093628749981011408838413 := by
  apply lucas_primality 146601093628749981011408838413 (2 : ZMod 146601093628749981011408838413)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (463, 1), (3449, 1), (22951075064915360481269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (463, 1), (3449, 1), (22951075064915360481269, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_463
      · exact prime_oneHundredTwentyFourDR_3449
      · exact prime_oneHundredTwentyFourDR_22951075064915360481269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 146601093628749981011408838413) ^ 73300546814374990505704419206 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 146601093628749981011408838413) ^ 316633031595572313199587124 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 146601093628749981011408838413) ^ 42505391020223247611310188 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (2 : ZMod 146601093628749981011408838413) ^ 6387548 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_146601093628749981011408838449 : Nat.Prime 146601093628749981011408838449 := by
  apply lucas_primality 146601093628749981011408838449 (3 : ZMod 146601093628749981011408838449)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (64360559390279, 1), (142363093773557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (64360559390279, 1), (142363093773557, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_64360559390279
      · exact prime_oneHundredTwentyFourDR_142363093773557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 146601093628749981011408838449) ^ 73300546814374990505704419224 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 146601093628749981011408838449) ^ 2277809500376912 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 146601093628749981011408838449) ^ 1029768950244464 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_146601093628749981011408838463 : Nat.Prime 146601093628749981011408838463 := by
  apply lucas_primality 146601093628749981011408838463 (5 : ZMod 146601093628749981011408838463)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (31, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (31, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_3
      · exact prime_oneHundredTwentyFourDR_11
      · exact prime_oneHundredTwentyFourDR_31
      · exact prime_oneHundredTwentyFourDR_461
      · exact prime_oneHundredTwentyFourDR_69997
      · exact prime_oneHundredTwentyFourDR_2220502305087140441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 146601093628749981011408838463) ^ 73300546814374990505704419231 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838463) ^ 48867031209583327003802946154 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838463) ^ 13327372148068180091946258042 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838463) ^ 4729067536411289710045446402 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838463) ^ 318006710691431629091993142 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838463) ^ 2094391097172021386793846 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (5 : ZMod 146601093628749981011408838463) ^ 66021590382 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFourDR_146601093628749981011408838497 : Nat.Prime 146601093628749981011408838497 := by
  apply lucas_primality 146601093628749981011408838497 (3 : ZMod 146601093628749981011408838497)
  · rw [← oneHundredTwentyFourDRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19743949, 1), (232034846519226569447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19743949, 1), (232034846519226569447, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFourDR_2
      · exact prime_oneHundredTwentyFourDR_19743949
      · exact prime_oneHundredTwentyFourDR_232034846519226569447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 146601093628749981011408838497) ^ 73300546814374990505704419248 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 146601093628749981011408838497) ^ 7425115088615250222304 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide
    · change (3 : ZMod 146601093628749981011408838497) ^ 631806368 ≠ 1
      rw [← oneHundredTwentyFourDRFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838400 : Nat.totient 146601093628749981011408838400 = 56748479260082249026990080000 := by
  rw [← show ((([(2, 8), (5, 2), (31, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_31, prime_oneHundredTwentyFourDR_171401, prime_oneHundredTwentyFourDR_714027719, prime_oneHundredTwentyFourDR_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838401 : Nat.totient 146601093628749981011408838401 = 145533934894838194526285999808 := by
  rw [← show ((([(157, 1), (1093, 1), (1204139, 1), (709481005865533459, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_157, prime_oneHundredTwentyFourDR_1093, prime_oneHundredTwentyFourDR_1204139, prime_oneHundredTwentyFourDR_709481005865533459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838402 : Nat.totient 146601093628749981011408838402 = 38620234799250565039950728448 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (13, 1), (883, 1), (13909117, 1), (21861718784556967, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_13, prime_oneHundredTwentyFourDR_883, prime_oneHundredTwentyFourDR_13909117, prime_oneHundredTwentyFourDR_21861718784556967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838403 : Nat.totient 146601093628749981011408838403 = 146601093628749981011408838402 := by
  rw [← show ((([(146601093628749981011408838403, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_146601093628749981011408838403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838404 : Nat.totient 146601093628749981011408838404 = 69435799811212270501330638336 := by
  rw [← show ((([(2, 2), (19, 1), (10177, 1), (189541294907440902617627, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_19, prime_oneHundredTwentyFourDR_10177, prime_oneHundredTwentyFourDR_189541294907440902617627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838405 : Nat.totient 146601093628749981011408838405 = 78015057129121482267060124800 := by
  rw [← show ((([(3, 3), (5, 1), (487, 2), (6701, 1), (683291315954695087, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_487, prime_oneHundredTwentyFourDR_6701, prime_oneHundredTwentyFourDR_683291315954695087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838406 : Nat.totient 146601093628749981011408838406 = 73300546805220232974720221880 := by
  rw [← show ((([(2, 1), (8006825591, 1), (9154757522977371733, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_8006825591, prime_oneHundredTwentyFourDR_9154757522977371733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838407 : Nat.totient 146601093628749981011408838407 = 133273721480681800919462580260 := by
  rw [← show ((([(11, 2), (1211579286188016371995114367, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_1211579286188016371995114367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838408 : Nat.totient 146601093628749981011408838408 = 48867031113276876450109337600 := by
  rw [← show ((([(2, 3), (3, 1), (966324071, 1), (1399501757, 1), (4516788161, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_966324071, prime_oneHundredTwentyFourDR_1399501757, prime_oneHundredTwentyFourDR_4516788161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838409 : Nat.totient 146601093628749981011408838409 = 125657414271582556577650882080 := by
  rw [← show ((([(7, 1), (188681, 1), (110996938618810116403127, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_188681, prime_oneHundredTwentyFourDR_110996938618810116403127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838410 : Nat.totient 146601093628749981011408838410 = 54030925054322856394063626240 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (127, 1), (179, 1), (239, 1), (307, 1), (4283, 1), (21341, 1), (5656299799, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_17, prime_oneHundredTwentyFourDR_127, prime_oneHundredTwentyFourDR_179, prime_oneHundredTwentyFourDR_239, prime_oneHundredTwentyFourDR_307, prime_oneHundredTwentyFourDR_4283, prime_oneHundredTwentyFourDR_21341, prime_oneHundredTwentyFourDR_5656299799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838411 : Nat.totient 146601093628749981011408838411 = 97557547407046525760559084800 := by
  rw [← show ((([(3, 1), (557, 1), (92921, 1), (944162800047756383621, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_557, prime_oneHundredTwentyFourDR_92921, prime_oneHundredTwentyFourDR_944162800047756383621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838412 : Nat.totient 146601093628749981011408838412 = 73121023505217222556016747136 := by
  rw [← show ((([(2, 2), (463, 1), (3449, 1), (22951075064915360481269, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_463, prime_oneHundredTwentyFourDR_3449, prime_oneHundredTwentyFourDR_22951075064915360481269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838413 : Nat.totient 146601093628749981011408838413 = 146601093628749981011408838412 := by
  rw [← show ((([(146601093628749981011408838413, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_146601093628749981011408838413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838414 : Nat.totient 146601093628749981011408838414 = 48867031209583327003802946132 := by
  rw [← show ((([(2, 1), (3, 2), (8144505201597221167300491023, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_8144505201597221167300491023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838415 : Nat.totient 146601093628749981011408838415 = 104526190810897622090997657600 := by
  rw [← show ((([(5, 1), (13, 1), (29, 1), (1243119329, 1), (62562347515013051, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_13, prime_oneHundredTwentyFourDR_29, prime_oneHundredTwentyFourDR_1243119329, prime_oneHundredTwentyFourDR_62562347515013051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838416 : Nat.totient 146601093628749981011408838416 = 62505106552711585996320890880 := by
  rw [← show ((([(2, 4), (7, 2), (353, 1), (431, 1), (106747, 1), (11513662460653469, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_353, prime_oneHundredTwentyFourDR_431, prime_oneHundredTwentyFourDR_106747, prime_oneHundredTwentyFourDR_11513662460653469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838417 : Nat.totient 146601093628749981011408838417 = 96272089973484817533092937216 := by
  rw [← show ((([(3, 1), (67, 1), (35797, 1), (171007, 1), (36877667, 1), (3230852969, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_67, prime_oneHundredTwentyFourDR_35797, prime_oneHundredTwentyFourDR_171007, prime_oneHundredTwentyFourDR_36877667, prime_oneHundredTwentyFourDR_3230852969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838418 : Nat.totient 146601093628749981011408838418 = 66616707353441443824327839760 := by
  rw [← show ((([(2, 1), (11, 1), (3307, 1), (21203759, 1), (95031476064490463, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_3307, prime_oneHundredTwentyFourDR_21203759, prime_oneHundredTwentyFourDR_95031476064490463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838419 : Nat.totient 146601093628749981011408838419 = 137850401967785538519202414216 := by
  rw [← show ((([(23, 1), (59, 1), (108033230382277067805017567, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_23, prime_oneHundredTwentyFourDR_59, prime_oneHundredTwentyFourDR_108033230382277067805017567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838420 : Nat.totient 146601093628749981011408838420 = 39056139851017159242520169472 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (1259, 1), (6073, 1), (24177523, 1), (13217372915987, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_1259, prime_oneHundredTwentyFourDR_6073, prime_oneHundredTwentyFourDR_24177523, prime_oneHundredTwentyFourDR_13217372915987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838421 : Nat.totient 146601093628749981011408838421 = 146600763351635516401078387072 := by
  rw [← show ((([(443873, 1), (330277114464610330007477, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_443873, prime_oneHundredTwentyFourDR_330277114464610330007477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838422 : Nat.totient 146601093628749981011408838422 = 72871451140222324096660506432 := by
  rw [← show ((([(2, 1), (173, 1), (13513, 1), (31355182619851400003039, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_173, prime_oneHundredTwentyFourDR_13513, prime_oneHundredTwentyFourDR_31355182619851400003039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838423 : Nat.totient 146601093628749981011408838423 = 78353875547405588037472680960 := by
  rw [← show ((([(3, 2), (7, 1), (19, 1), (83, 1), (1481, 1), (996345374177602247033, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_19, prime_oneHundredTwentyFourDR_83, prime_oneHundredTwentyFourDR_1481, prime_oneHundredTwentyFourDR_996345374177602247033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838424 : Nat.totient 146601093628749981011408838424 = 73300546814374990505704419208 := by
  rw [← show ((([(2, 3), (18325136703593747626426104803, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_18325136703593747626426104803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838425 : Nat.totient 146601093628749981011408838425 = 111930203223540672594912960000 := by
  rw [← show ((([(5, 2), (41, 1), (47, 1), (2011, 1), (1513224681261365355221, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_41, prime_oneHundredTwentyFourDR_47, prime_oneHundredTwentyFourDR_2011, prime_oneHundredTwentyFourDR_1513224681261365355221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838426 : Nat.totient 146601093628749981011408838426 = 47941498914788545837756876800 := by
  rw [← show ((([(2, 1), (3, 1), (53, 1), (13649, 1), (381716201, 1), (88484797934443, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_53, prime_oneHundredTwentyFourDR_13649, prime_oneHundredTwentyFourDR_381716201, prime_oneHundredTwentyFourDR_88484797934443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838427 : Nat.totient 146601093628749981011408838427 = 137909100799752335114392349184 := by
  rw [← show ((([(17, 1), (3623, 1), (4567, 1), (1233437, 1), (422544030970343, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_17, prime_oneHundredTwentyFourDR_3623, prime_oneHundredTwentyFourDR_4567, prime_oneHundredTwentyFourDR_1233437, prime_oneHundredTwentyFourDR_422544030970343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838428 : Nat.totient 146601093628749981011408838428 = 67541815428096839676948283392 := by
  rw [← show ((([(2, 2), (13, 1), (953, 1), (1373, 1), (1114172737, 1), (1933828254263, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_13, prime_oneHundredTwentyFourDR_953, prime_oneHundredTwentyFourDR_1373, prime_oneHundredTwentyFourDR_1114172737, prime_oneHundredTwentyFourDR_1933828254263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838429 : Nat.totient 146601093628749981011408838429 = 86447351044203838895195976960 := by
  rw [← show ((([(3, 1), (11, 1), (37, 2), (189479, 1), (7171079, 1), (2388219450997, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_37, prime_oneHundredTwentyFourDR_189479, prime_oneHundredTwentyFourDR_7171079, prime_oneHundredTwentyFourDR_2388219450997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838430 : Nat.totient 146601093628749981011408838430 = 49574694039452638052422938624 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (73, 1), (77973617, 1), (367932905030454989, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_73, prime_oneHundredTwentyFourDR_77973617, prime_oneHundredTwentyFourDR_367932905030454989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838431 : Nat.totient 146601093628749981011408838431 = 141853262374576109898978091200 := by
  rw [← show ((([(31, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_31, prime_oneHundredTwentyFourDR_7561, prime_oneHundredTwentyFourDR_2416168199, prime_oneHundredTwentyFourDR_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838432 : Nat.totient 146601093628749981011408838432 = 48566220208900633959644528640 := by
  rw [← show ((([(2, 5), (3, 3), (193, 1), (1021, 1), (8184194567, 1), (105211804913, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_193, prime_oneHundredTwentyFourDR_1021, prime_oneHundredTwentyFourDR_8184194567, prime_oneHundredTwentyFourDR_105211804913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838433 : Nat.totient 146601093628749981011408838433 = 146601093619640770532121117888 := by
  rw [← show ((([(16093721209, 1), (9109210463193999337, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_16093721209, prime_oneHundredTwentyFourDR_9109210463193999337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838434 : Nat.totient 146601093628749981011408838434 = 71448016048618926420026370432 := by
  rw [← show ((([(2, 1), (43, 1), (523, 1), (6659, 1), (296363, 1), (1651596952044409, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_43, prime_oneHundredTwentyFourDR_523, prime_oneHundredTwentyFourDR_6659, prime_oneHundredTwentyFourDR_296363, prime_oneHundredTwentyFourDR_1651596952044409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838435 : Nat.totient 146601093628749981011408838435 = 78046172690262034525575340032 := by
  rw [← show ((([(3, 1), (5, 1), (859, 1), (1619, 1), (42953, 1), (48906269, 1), (3345398857, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_859, prime_oneHundredTwentyFourDR_1619, prime_oneHundredTwentyFourDR_42953, prime_oneHundredTwentyFourDR_48906269, prime_oneHundredTwentyFourDR_3345398857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838436 : Nat.totient 146601093628749981011408838436 = 73300546814374990505704419216 := by
  rw [← show ((([(2, 2), (36650273407187495252852209609, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_36650273407187495252852209609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838437 : Nat.totient 146601093628749981011408838437 = 125620804050232004748514058400 := by
  rw [← show ((([(7, 1), (3371, 1), (6212700497044114972725721, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_3371, prime_oneHundredTwentyFourDR_6212700497044114972725721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838438 : Nat.totient 146601093628749981011408838438 = 48867031209583327003802946144 := by
  rw [← show ((([(2, 1), (3, 1), (24433515604791663501901473073, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_24433515604791663501901473073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838439 : Nat.totient 146601093628749981011408838439 = 145790898996139734075682003200 := by
  rw [← show ((([(181, 1), (597899, 1), (1354661562452864814881, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_181, prime_oneHundredTwentyFourDR_597899, prime_oneHundredTwentyFourDR_1354661562452864814881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838440 : Nat.totient 146601093628749981011408838440 = 52388870149632047291119411200 := by
  rw [← show ((([(2, 3), (5, 1), (11, 1), (61, 1), (1123, 1), (23242647853, 1), (209261502889, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_61, prime_oneHundredTwentyFourDR_1123, prime_oneHundredTwentyFourDR_23242647853, prime_oneHundredTwentyFourDR_209261502889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838441 : Nat.totient 146601093628749981011408838441 = 90215475837596869504639700736 := by
  rw [← show ((([(3, 2), (13, 1), (155069, 1), (8080279103145866249417, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_13, prime_oneHundredTwentyFourDR_155069, prime_oneHundredTwentyFourDR_8080279103145866249417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838442 : Nat.totient 146601093628749981011408838442 = 65706867692806696931836800000 := by
  rw [← show ((([(2, 1), (19, 1), (23, 1), (197, 1), (311, 1), (421, 1), (7451, 1), (42359, 1), (20604249691, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_19, prime_oneHundredTwentyFourDR_23, prime_oneHundredTwentyFourDR_197, prime_oneHundredTwentyFourDR_311, prime_oneHundredTwentyFourDR_421, prime_oneHundredTwentyFourDR_7451, prime_oneHundredTwentyFourDR_42359, prime_oneHundredTwentyFourDR_20604249691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838443 : Nat.totient 146601093628749981011408838443 = 144704506603549897428925288320 := by
  rw [← show ((([(79, 1), (3541, 1), (524063836750506654457937, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_79, prime_oneHundredTwentyFourDR_3541, prime_oneHundredTwentyFourDR_524063836750506654457937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838444 : Nat.totient 146601093628749981011408838444 = 38017370711671900092570636288 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (17, 1), (29, 1), (839, 1), (1805059, 1), (2337532415679887, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_17, prime_oneHundredTwentyFourDR_29, prime_oneHundredTwentyFourDR_839, prime_oneHundredTwentyFourDR_1805059, prime_oneHundredTwentyFourDR_2337532415679887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838445 : Nat.totient 146601093628749981011408838445 = 116213912145057148088133196800 := by
  rw [← show ((([(5, 1), (113, 1), (6211, 1), (13799, 1), (59887, 1), (50553014800571, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_113, prime_oneHundredTwentyFourDR_6211, prime_oneHundredTwentyFourDR_13799, prime_oneHundredTwentyFourDR_59887, prime_oneHundredTwentyFourDR_50553014800571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838446 : Nat.totient 146601093628749981011408838446 = 73299542813404415987686646400 := by
  rw [← show ((([(2, 1), (73009, 1), (9556376147, 1), (105060044122301, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_73009, prime_oneHundredTwentyFourDR_9556376147, prime_oneHundredTwentyFourDR_105060044122301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838447 : Nat.totient 146601093628749981011408838447 = 97223854341327734630193645600 := by
  rw [← show ((([(3, 1), (211, 1), (2069, 1), (111936831469705874816011, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_211, prime_oneHundredTwentyFourDR_2069, prime_oneHundredTwentyFourDR_111936831469705874816011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838448 : Nat.totient 146601093628749981011408838448 = 73300546814373336716479108544 := by
  rw [← show ((([(2, 4), (64360559390279, 1), (142363093773557, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_64360559390279, prime_oneHundredTwentyFourDR_142363093773557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838449 : Nat.totient 146601093628749981011408838449 = 146601093628749981011408838448 := by
  rw [← show ((([(146601093628749981011408838449, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_146601093628749981011408838449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838450 : Nat.totient 146601093628749981011408838450 = 39093391331990425280375677440 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (234659, 1), (583153, 1), (2380701615042083, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_234659, prime_oneHundredTwentyFourDR_583153, prime_oneHundredTwentyFourDR_2380701615042083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838451 : Nat.totient 146601093628749981011408838451 = 114090665693387729962864158720 := by
  rw [← show ((([(7, 1), (11, 1), (1229, 1), (2239, 1), (4634837, 1), (149281518186929, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_1229, prime_oneHundredTwentyFourDR_2239, prime_oneHundredTwentyFourDR_4634837, prime_oneHundredTwentyFourDR_149281518186929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838452 : Nat.totient 146601093628749981011408838452 = 71410024886690900904139296000 := by
  rw [← show ((([(2, 2), (71, 1), (109, 1), (367, 1), (12904058043247987123801, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_71, prime_oneHundredTwentyFourDR_109, prime_oneHundredTwentyFourDR_367, prime_oneHundredTwentyFourDR_12904058043247987123801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838453 : Nat.totient 146601093628749981011408838453 = 97702720461545953842603962160 := by
  rw [← show ((([(3, 1), (3119, 1), (14171471, 1), (1105568479646925799, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_3119, prime_oneHundredTwentyFourDR_14171471, prime_oneHundredTwentyFourDR_1105568479646925799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838454 : Nat.totient 146601093628749981011408838454 = 67556484139185840540602695680 := by
  rw [← show ((([(2, 1), (13, 1), (641, 1), (38273129, 1), (337822627, 1), (680335493, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_13, prime_oneHundredTwentyFourDR_641, prime_oneHundredTwentyFourDR_38273129, prime_oneHundredTwentyFourDR_337822627, prime_oneHundredTwentyFourDR_680335493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838455 : Nat.totient 146601093628749981011408838455 = 117280874902999984809127070760 := by
  rw [← show ((([(5, 1), (29320218725749996202281767691, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_29320218725749996202281767691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838456 : Nat.totient 146601093628749981011408838456 = 48858710137903197244192296960 := by
  rw [← show ((([(2, 3), (3, 1), (5897, 1), (1424021, 1), (727408625826681937, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_5897, prime_oneHundredTwentyFourDR_1424021, prime_oneHundredTwentyFourDR_727408625826681937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838457 : Nat.totient 146601093628749981011408838457 = 146556923368542463692634683636 := by
  rw [← show ((([(3319, 1), (44170260207517318774151503, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3319, prime_oneHundredTwentyFourDR_44170260207517318774151503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838458 : Nat.totient 146601093628749981011408838458 = 62672357247759820912066560000 := by
  rw [← show ((([(2, 1), (7, 1), (401, 1), (52870897, 1), (79810561, 1), (6188533691, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_401, prime_oneHundredTwentyFourDR_52870897, prime_oneHundredTwentyFourDR_79810561, prime_oneHundredTwentyFourDR_6188533691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838459 : Nat.totient 146601093628749981011408838459 = 97734062419166654007605879184 := by
  rw [← show ((([(3, 9), (7448107180244372352355273, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_7448107180244372352355273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838460 : Nat.totient 146601093628749981011408838460 = 57752348630342228669874659328 := by
  rw [← show ((([(2, 2), (5, 1), (89, 1), (433, 1), (607, 1), (313357880006437214197, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_89, prime_oneHundredTwentyFourDR_433, prime_oneHundredTwentyFourDR_607, prime_oneHundredTwentyFourDR_313357880006437214197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838461 : Nat.totient 146601093628749981011408838461 = 130715526207594434579716449024 := by
  rw [← show ((([(17, 2), (19, 1), (1741983823259, 1), (15326452682269, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_17, prime_oneHundredTwentyFourDR_19, prime_oneHundredTwentyFourDR_1741983823259, prime_oneHundredTwentyFourDR_15326452682269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838462 : Nat.totient 146601093628749981011408838462 = 42897653099738737097754240000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (31, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_31, prime_oneHundredTwentyFourDR_461, prime_oneHundredTwentyFourDR_69997, prime_oneHundredTwentyFourDR_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838463 : Nat.totient 146601093628749981011408838463 = 146601093628749981011408838462 := by
  rw [← show ((([(146601093628749981011408838463, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_146601093628749981011408838463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838464 : Nat.totient 146601093628749981011408838464 = 73300546814374990505704419200 := by
  rw [← show ((([(2, 6), (2290642087949218453303263101, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_2290642087949218453303263101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838465 : Nat.totient 146601093628749981011408838465 = 64054407547935954771389881344 := by
  rw [← show ((([(3, 1), (5, 1), (7, 3), (23, 1), (1297, 1), (955177357414373605007, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_23, prime_oneHundredTwentyFourDR_1297, prime_oneHundredTwentyFourDR_955177357414373605007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838466 : Nat.totient 146601093628749981011408838466 = 69579766037051343898455398400 := by
  rw [← show ((([(2, 1), (37, 1), (41, 1), (374461, 1), (231958477, 1), (556294533517, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_37, prime_oneHundredTwentyFourDR_41, prime_oneHundredTwentyFourDR_374461, prime_oneHundredTwentyFourDR_231958477, prime_oneHundredTwentyFourDR_556294533517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838467 : Nat.totient 146601093628749981011408838467 = 135229387975575156086101175520 := by
  rw [← show ((([(13, 1), (1429, 1), (7891537580273993702503571, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_13, prime_oneHundredTwentyFourDR_1429, prime_oneHundredTwentyFourDR_7891537580273993702503571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838468 : Nat.totient 146601093628749981011408838468 = 48247965529908778493022271680 := by
  rw [← show ((([(2, 2), (3, 2), (131, 1), (199, 1), (20563, 1), (7596680508025691879, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_131, prime_oneHundredTwentyFourDR_199, prime_oneHundredTwentyFourDR_20563, prime_oneHundredTwentyFourDR_7596680508025691879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838469 : Nat.totient 146601093628749981011408838469 = 146353874183991683538900748800 := by
  rw [← show ((([(593, 1), (2338480733, 1), (105717946992070201, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_593, prime_oneHundredTwentyFourDR_2338480733, prime_oneHundredTwentyFourDR_105717946992070201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838470 : Nat.totient 146601093628749981011408838470 = 58640437450614789734954130624 := by
  rw [← show ((([(2, 1), (5, 1), (66245230633, 1), (221300601157120559, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_66245230633, prime_oneHundredTwentyFourDR_221300601157120559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838471 : Nat.totient 146601093628749981011408838471 = 97734062419166654007605892312 := by
  rw [← show ((([(3, 1), (48867031209583327003802946157, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_48867031209583327003802946157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838472 : Nat.totient 146601093628749981011408838472 = 60857846810427993427068549120 := by
  rw [← show ((([(2, 3), (7, 1), (47, 1), (97, 1), (131023, 1), (4382602193503262191, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_47, prime_oneHundredTwentyFourDR_97, prime_oneHundredTwentyFourDR_131023, prime_oneHundredTwentyFourDR_4382602193503262191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838473 : Nat.totient 146601093628749981011408838473 = 128658741447636857199114227520 := by
  rw [← show ((([(11, 1), (29, 1), (9619, 1), (21599, 1), (2211988974136255507, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_29, prime_oneHundredTwentyFourDR_9619, prime_oneHundredTwentyFourDR_21599, prime_oneHundredTwentyFourDR_2211988974136255507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838474 : Nat.totient 146601093628749981011408838474 = 48829179130566057103308205680 := by
  rw [← show ((([(2, 1), (3, 1), (1291, 1), (22500583207, 1), (841135460775667, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_1291, prime_oneHundredTwentyFourDR_22500583207, prime_oneHundredTwentyFourDR_841135460775667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838475 : Nat.totient 146601093628749981011408838475 = 117261861880567388109411801600 := by
  rw [← show ((([(5, 2), (9181, 1), (18797, 1), (2291598263, 1), (14827918429, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_9181, prime_oneHundredTwentyFourDR_18797, prime_oneHundredTwentyFourDR_2291598263, prime_oneHundredTwentyFourDR_14827918429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838476 : Nat.totient 146601093628749981011408838476 = 73300546811591557160287788288 := by
  rw [← show ((([(2, 2), (26334580033, 1), (1391716646373735443, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_26334580033, prime_oneHundredTwentyFourDR_1391716646373735443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838477 : Nat.totient 146601093628749981011408838477 = 95421060373225102992875750400 := by
  rw [← show ((([(3, 2), (43, 1), (2381, 1), (5549209, 1), (14161111, 1), (2024596309, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_43, prime_oneHundredTwentyFourDR_2381, prime_oneHundredTwentyFourDR_5549209, prime_oneHundredTwentyFourDR_14161111, prime_oneHundredTwentyFourDR_2024596309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838478 : Nat.totient 146601093628749981011408838478 = 67816906089622619824183471104 := by
  rw [← show ((([(2, 1), (17, 1), (59, 1), (26669, 1), (2740309081917507835177, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_17, prime_oneHundredTwentyFourDR_59, prime_oneHundredTwentyFourDR_26669, prime_oneHundredTwentyFourDR_2740309081917507835177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838479 : Nat.totient 146601093628749981011408838479 = 123272832358248605206260882432 := by
  rw [← show ((([(7, 1), (53, 1), (8597, 1), (45963847361268436275617, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_53, prime_oneHundredTwentyFourDR_8597, prime_oneHundredTwentyFourDR_45963847361268436275617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838480 : Nat.totient 146601093628749981011408838480 = 34187135436185567016152918016 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (13, 1), (19, 1), (15629399, 1), (158229238067428459, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_13, prime_oneHundredTwentyFourDR_19, prime_oneHundredTwentyFourDR_15629399, prime_oneHundredTwentyFourDR_158229238067428459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838481 : Nat.totient 146601093628749981011408838481 = 146572237722056887145558108160 := by
  rw [← show ((([(5081, 1), (47229857, 1), (610901771565687193, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_5081, prime_oneHundredTwentyFourDR_47229857, prime_oneHundredTwentyFourDR_610901771565687193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838482 : Nat.totient 146601093628749981011408838482 = 72985952192854067799671352832 := by
  rw [← show ((([(2, 1), (233, 1), (314594621520922706033066177, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_233, prime_oneHundredTwentyFourDR_314594621520922706033066177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838483 : Nat.totient 146601093628749981011408838483 = 97734062419116061081714115304 := by
  rw [← show ((([(3, 1), (1931920823563, 1), (25294531025064947, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_1931920823563, prime_oneHundredTwentyFourDR_25294531025064947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838484 : Nat.totient 146601093628749981011408838484 = 64806859968752294660305843200 := by
  rw [← show ((([(2, 2), (11, 1), (67, 1), (107, 1), (293, 1), (324964763, 1), (4881148959241, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_67, prime_oneHundredTwentyFourDR_107, prime_oneHundredTwentyFourDR_293, prime_oneHundredTwentyFourDR_324964763, prime_oneHundredTwentyFourDR_4881148959241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838485 : Nat.totient 146601093628749981011408838485 = 117280874899866366545973512400 := by
  rw [← show ((([(5, 1), (37426664851, 1), (783404528361724747, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_37426664851, prime_oneHundredTwentyFourDR_783404528361724747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838486 : Nat.totient 146601093628749981011408838486 = 41886025761218677963110270720 := by
  rw [← show ((([(2, 1), (3, 3), (7, 1), (51603691, 1), (236850169, 1), (31731525053, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_51603691, prime_oneHundredTwentyFourDR_236850169, prime_oneHundredTwentyFourDR_31731525053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838487 : Nat.totient 146601093628749981011408838487 = 145833540420875278311337676640 := by
  rw [← show ((([(191, 1), (17751989, 1), (43237126432462330213, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_191, prime_oneHundredTwentyFourDR_17751989, prime_oneHundredTwentyFourDR_43237126432462330213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838488 : Nat.totient 146601093628749981011408838488 = 70104197472573274472619881856 := by
  rw [← show ((([(2, 3), (23, 1), (7487, 1), (16161127, 1), (6584759398665493, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_23, prime_oneHundredTwentyFourDR_7487, prime_oneHundredTwentyFourDR_16161127, prime_oneHundredTwentyFourDR_6584759398665493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838489 : Nat.totient 146601093628749981011408838489 = 97693152388853063947326437616 := by
  rw [← show ((([(3, 1), (2389, 1), (20455015156795030139724967, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_2389, prime_oneHundredTwentyFourDR_20455015156795030139724967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838490 : Nat.totient 146601093628749981011408838490 = 58640402116068418270529856000 := by
  rw [← show ((([(2, 1), (5, 1), (1699001, 1), (71445277, 1), (120773054768837, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_1699001, prime_oneHundredTwentyFourDR_71445277, prime_oneHundredTwentyFourDR_120773054768837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838491 : Nat.totient 146601093628749981011408838491 = 146601077615773053316225395912 := by
  rw [← show ((([(9155143, 1), (16012976927695174287437, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_9155143, prime_oneHundredTwentyFourDR_16012976927695174287437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838492 : Nat.totient 146601093628749981011408838492 = 48867031209577826565872042736 := by
  rw [← show ((([(2, 2), (3, 1), (8942359683779, 1), (1366167123042079, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_8942359683779, prime_oneHundredTwentyFourDR_1366167123042079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838493 : Nat.totient 146601093628749981011408838493 = 109923657307797650024171520000 := by
  rw [← show ((([(7, 1), (13, 1), (31, 1), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_13, prime_oneHundredTwentyFourDR_31, prime_oneHundredTwentyFourDR_101, prime_oneHundredTwentyFourDR_103, prime_oneHundredTwentyFourDR_1163, prime_oneHundredTwentyFourDR_3221, prime_oneHundredTwentyFourDR_20357, prime_oneHundredTwentyFourDR_53279, prime_oneHundredTwentyFourDR_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838494 : Nat.totient 146601093628749981011408838494 = 73210160730875908175731080000 := by
  rw [← show ((([(2, 1), (811, 1), (23130377, 1), (3907541947548230501, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_811, prime_oneHundredTwentyFourDR_23130377, prime_oneHundredTwentyFourDR_3907541947548230501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838495 : Nat.totient 146601093628749981011408838495 = 66889539677184228029000908800 := by
  rw [← show ((([(3, 2), (5, 1), (11, 1), (17, 1), (7741, 1), (2553160849, 1), (881470629317, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_11, prime_oneHundredTwentyFourDR_17, prime_oneHundredTwentyFourDR_7741, prime_oneHundredTwentyFourDR_2553160849, prime_oneHundredTwentyFourDR_881470629317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838496 : Nat.totient 146601093628749981011408838496 = 73300543101817446197763404928 := by
  rw [← show ((([(2, 5), (19743949, 1), (232034846519226569447, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_19743949, prime_oneHundredTwentyFourDR_232034846519226569447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838497 : Nat.totient 146601093628749981011408838497 = 146601093628749981011408838496 := by
  rw [← show ((([(146601093628749981011408838497, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_146601093628749981011408838497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838498 : Nat.totient 146601093628749981011408838498 = 48867031136612179282496879136 := by
  rw [← show ((([(2, 1), (3, 1), (669676067, 1), (36485573859983357449, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_669676067, prime_oneHundredTwentyFourDR_36485573859983357449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838499 : Nat.totient 146601093628749981011408838499 = 138885246595657876747650478560 := by
  rw [← show ((([(19, 1), (7715847033092104263758359921, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_19, prime_oneHundredTwentyFourDR_7715847033092104263758359921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838500 : Nat.totient 146601093628749981011408838500 = 50262057299658013413343113600 := by
  rw [← show ((([(2, 2), (5, 3), (7, 1), (42787, 1), (716002187, 1), (1367234409419, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_2, prime_oneHundredTwentyFourDR_5, prime_oneHundredTwentyFourDR_7, prime_oneHundredTwentyFourDR_42787, prime_oneHundredTwentyFourDR_716002187, prime_oneHundredTwentyFourDR_1367234409419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFourDR_146601093628749981011408838501 : Nat.totient 146601093628749981011408838501 = 96128347095954548600184422400 := by
  rw [← show ((([(3, 1), (61, 1), (27329, 1), (74714424371, 1), (392335787633, 1)] : List FactorBlock).map factorBlockValue).prod) = 146601093628749981011408838501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFourDR_3, prime_oneHundredTwentyFourDR_61, prime_oneHundredTwentyFourDR_27329, prime_oneHundredTwentyFourDR_74714424371, prime_oneHundredTwentyFourDR_392335787633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentyFourDR : certifiedKill 1 146601093628749981011408838399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentyFourDR_146601093628749981011408838400, phi_oneHundredTwentyFourDR_146601093628749981011408838401, phi_oneHundredTwentyFourDR_146601093628749981011408838402,
    phi_oneHundredTwentyFourDR_146601093628749981011408838403, phi_oneHundredTwentyFourDR_146601093628749981011408838404, phi_oneHundredTwentyFourDR_146601093628749981011408838405,
    phi_oneHundredTwentyFourDR_146601093628749981011408838406, phi_oneHundredTwentyFourDR_146601093628749981011408838407, phi_oneHundredTwentyFourDR_146601093628749981011408838408,
    phi_oneHundredTwentyFourDR_146601093628749981011408838409, phi_oneHundredTwentyFourDR_146601093628749981011408838410, phi_oneHundredTwentyFourDR_146601093628749981011408838411,
    phi_oneHundredTwentyFourDR_146601093628749981011408838412, phi_oneHundredTwentyFourDR_146601093628749981011408838413, phi_oneHundredTwentyFourDR_146601093628749981011408838414,
    phi_oneHundredTwentyFourDR_146601093628749981011408838415, phi_oneHundredTwentyFourDR_146601093628749981011408838416, phi_oneHundredTwentyFourDR_146601093628749981011408838417,
    phi_oneHundredTwentyFourDR_146601093628749981011408838418, phi_oneHundredTwentyFourDR_146601093628749981011408838419, phi_oneHundredTwentyFourDR_146601093628749981011408838420,
    phi_oneHundredTwentyFourDR_146601093628749981011408838421, phi_oneHundredTwentyFourDR_146601093628749981011408838422, phi_oneHundredTwentyFourDR_146601093628749981011408838423,
    phi_oneHundredTwentyFourDR_146601093628749981011408838424, phi_oneHundredTwentyFourDR_146601093628749981011408838425, phi_oneHundredTwentyFourDR_146601093628749981011408838426,
    phi_oneHundredTwentyFourDR_146601093628749981011408838427, phi_oneHundredTwentyFourDR_146601093628749981011408838428, phi_oneHundredTwentyFourDR_146601093628749981011408838429,
    phi_oneHundredTwentyFourDR_146601093628749981011408838430, phi_oneHundredTwentyFourDR_146601093628749981011408838431, phi_oneHundredTwentyFourDR_146601093628749981011408838432,
    phi_oneHundredTwentyFourDR_146601093628749981011408838433, phi_oneHundredTwentyFourDR_146601093628749981011408838434, phi_oneHundredTwentyFourDR_146601093628749981011408838435,
    phi_oneHundredTwentyFourDR_146601093628749981011408838436, phi_oneHundredTwentyFourDR_146601093628749981011408838437, phi_oneHundredTwentyFourDR_146601093628749981011408838438,
    phi_oneHundredTwentyFourDR_146601093628749981011408838439, phi_oneHundredTwentyFourDR_146601093628749981011408838440, phi_oneHundredTwentyFourDR_146601093628749981011408838441,
    phi_oneHundredTwentyFourDR_146601093628749981011408838442, phi_oneHundredTwentyFourDR_146601093628749981011408838443, phi_oneHundredTwentyFourDR_146601093628749981011408838444,
    phi_oneHundredTwentyFourDR_146601093628749981011408838445, phi_oneHundredTwentyFourDR_146601093628749981011408838446, phi_oneHundredTwentyFourDR_146601093628749981011408838447,
    phi_oneHundredTwentyFourDR_146601093628749981011408838448, phi_oneHundredTwentyFourDR_146601093628749981011408838449, phi_oneHundredTwentyFourDR_146601093628749981011408838450,
    phi_oneHundredTwentyFourDR_146601093628749981011408838451, phi_oneHundredTwentyFourDR_146601093628749981011408838452, phi_oneHundredTwentyFourDR_146601093628749981011408838453,
    phi_oneHundredTwentyFourDR_146601093628749981011408838454, phi_oneHundredTwentyFourDR_146601093628749981011408838455, phi_oneHundredTwentyFourDR_146601093628749981011408838456,
    phi_oneHundredTwentyFourDR_146601093628749981011408838457, phi_oneHundredTwentyFourDR_146601093628749981011408838458, phi_oneHundredTwentyFourDR_146601093628749981011408838459,
    phi_oneHundredTwentyFourDR_146601093628749981011408838460, phi_oneHundredTwentyFourDR_146601093628749981011408838461, phi_oneHundredTwentyFourDR_146601093628749981011408838462,
    phi_oneHundredTwentyFourDR_146601093628749981011408838463, phi_oneHundredTwentyFourDR_146601093628749981011408838464, phi_oneHundredTwentyFourDR_146601093628749981011408838465,
    phi_oneHundredTwentyFourDR_146601093628749981011408838466, phi_oneHundredTwentyFourDR_146601093628749981011408838467, phi_oneHundredTwentyFourDR_146601093628749981011408838468,
    phi_oneHundredTwentyFourDR_146601093628749981011408838469, phi_oneHundredTwentyFourDR_146601093628749981011408838470, phi_oneHundredTwentyFourDR_146601093628749981011408838471,
    phi_oneHundredTwentyFourDR_146601093628749981011408838472, phi_oneHundredTwentyFourDR_146601093628749981011408838473, phi_oneHundredTwentyFourDR_146601093628749981011408838474,
    phi_oneHundredTwentyFourDR_146601093628749981011408838475, phi_oneHundredTwentyFourDR_146601093628749981011408838476, phi_oneHundredTwentyFourDR_146601093628749981011408838477,
    phi_oneHundredTwentyFourDR_146601093628749981011408838478, phi_oneHundredTwentyFourDR_146601093628749981011408838479, phi_oneHundredTwentyFourDR_146601093628749981011408838480,
    phi_oneHundredTwentyFourDR_146601093628749981011408838481, phi_oneHundredTwentyFourDR_146601093628749981011408838482, phi_oneHundredTwentyFourDR_146601093628749981011408838483,
    phi_oneHundredTwentyFourDR_146601093628749981011408838484, phi_oneHundredTwentyFourDR_146601093628749981011408838485, phi_oneHundredTwentyFourDR_146601093628749981011408838486,
    phi_oneHundredTwentyFourDR_146601093628749981011408838487, phi_oneHundredTwentyFourDR_146601093628749981011408838488, phi_oneHundredTwentyFourDR_146601093628749981011408838489,
    phi_oneHundredTwentyFourDR_146601093628749981011408838490, phi_oneHundredTwentyFourDR_146601093628749981011408838491, phi_oneHundredTwentyFourDR_146601093628749981011408838492,
    phi_oneHundredTwentyFourDR_146601093628749981011408838493, phi_oneHundredTwentyFourDR_146601093628749981011408838494, phi_oneHundredTwentyFourDR_146601093628749981011408838495,
    phi_oneHundredTwentyFourDR_146601093628749981011408838496, phi_oneHundredTwentyFourDR_146601093628749981011408838497, phi_oneHundredTwentyFourDR_146601093628749981011408838498,
    phi_oneHundredTwentyFourDR_146601093628749981011408838499, phi_oneHundredTwentyFourDR_146601093628749981011408838500, phi_oneHundredTwentyFourDR_146601093628749981011408838501
    ]

end TotientTailPeriodKiller
end Erdos249257
