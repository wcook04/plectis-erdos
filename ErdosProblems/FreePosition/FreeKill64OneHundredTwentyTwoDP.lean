import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentyTwoDPFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentyTwoDPFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentyTwoDPFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentyTwoDPFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentyTwoDPFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentyTwoDPFastPow a n * oneHundredTwentyTwoDPFastPow a n * a else oneHundredTwentyTwoDPFastPow a n * oneHundredTwentyTwoDPFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentyTwoDP_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2503 : Nat.Prime 2503 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2531 : Nat.Prime 2531 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2969 : Nat.Prime 2969 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3727 : Nat.Prime 3727 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3821 : Nat.Prime 3821 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3907 : Nat.Prime 3907 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4159 : Nat.Prime 4159 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4297 : Nat.Prime 4297 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4583 : Nat.Prime 4583 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4973 : Nat.Prime 4973 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5059 : Nat.Prime 5059 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5261 : Nat.Prime 5261 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5351 : Nat.Prime 5351 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5381 : Nat.Prime 5381 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5407 : Nat.Prime 5407 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5441 : Nat.Prime 5441 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5519 : Nat.Prime 5519 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5527 : Nat.Prime 5527 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5581 : Nat.Prime 5581 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5647 : Nat.Prime 5647 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5827 : Nat.Prime 5827 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5849 : Nat.Prime 5849 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5861 : Nat.Prime 5861 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_6047 : Nat.Prime 6047 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_6311 : Nat.Prime 6311 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_6599 : Nat.Prime 6599 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_6967 : Nat.Prime 6967 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7103 : Nat.Prime 7103 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7229 : Nat.Prime 7229 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7297 : Nat.Prime 7297 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7417 : Nat.Prime 7417 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7457 : Nat.Prime 7457 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7823 : Nat.Prime 7823 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7853 : Nat.Prime 7853 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7873 : Nat.Prime 7873 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8039 : Nat.Prime 8039 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8387 : Nat.Prime 8387 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8431 : Nat.Prime 8431 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8537 : Nat.Prime 8537 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8863 : Nat.Prime 8863 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_9137 : Nat.Prime 9137 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_9343 : Nat.Prime 9343 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_9829 : Nat.Prime 9829 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_10337 : Nat.Prime 10337 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_10369 : Nat.Prime 10369 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_11003 : Nat.Prime 11003 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_12227 : Nat.Prime 12227 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_12269 : Nat.Prime 12269 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_12547 : Nat.Prime 12547 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_12919 : Nat.Prime 12919 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_13217 : Nat.Prime 13217 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_13337 : Nat.Prime 13337 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_13399 : Nat.Prime 13399 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_14083 : Nat.Prime 14083 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_14369 : Nat.Prime 14369 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_14759 : Nat.Prime 14759 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_14767 : Nat.Prime 14767 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_15073 : Nat.Prime 15073 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_15259 : Nat.Prime 15259 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_15773 : Nat.Prime 15773 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_16193 : Nat.Prime 16193 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_17041 : Nat.Prime 17041 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_17393 : Nat.Prime 17393 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_18047 : Nat.Prime 18047 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_18493 : Nat.Prime 18493 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_19571 : Nat.Prime 19571 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_20177 : Nat.Prime 20177 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_20231 : Nat.Prime 20231 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_21317 : Nat.Prime 21317 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_24001 : Nat.Prime 24001 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_24113 : Nat.Prime 24113 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_24371 : Nat.Prime 24371 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_24917 : Nat.Prime 24917 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_25087 : Nat.Prime 25087 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_28901 : Nat.Prime 28901 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_29059 : Nat.Prime 29059 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_30403 : Nat.Prime 30403 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_30859 : Nat.Prime 30859 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_32401 : Nat.Prime 32401 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_33811 : Nat.Prime 33811 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_37571 : Nat.Prime 37571 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_39313 : Nat.Prime 39313 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_39341 : Nat.Prime 39341 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_39883 : Nat.Prime 39883 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_42131 : Nat.Prime 42131 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_42589 : Nat.Prime 42589 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_43753 : Nat.Prime 43753 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_44563 : Nat.Prime 44563 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_46181 : Nat.Prime 46181 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_48121 : Nat.Prime 48121 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_49697 : Nat.Prime 49697 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_52747 : Nat.Prime 52747 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_58889 : Nat.Prime 58889 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_62351 : Nat.Prime 62351 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_63589 : Nat.Prime 63589 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_63781 : Nat.Prime 63781 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_64187 : Nat.Prime 64187 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_67153 : Nat.Prime 67153 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_69761 : Nat.Prime 69761 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_71777 : Nat.Prime 71777 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_72661 : Nat.Prime 72661 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_72949 : Nat.Prime 72949 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_73867 : Nat.Prime 73867 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_78173 : Nat.Prime 78173 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_78929 : Nat.Prime 78929 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_80233 : Nat.Prime 80233 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_85991 : Nat.Prime 85991 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_87187 : Nat.Prime 87187 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_91033 : Nat.Prime 91033 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_94441 : Nat.Prime 94441 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_95561 : Nat.Prime 95561 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_101449 : Nat.Prime 101449 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_102367 : Nat.Prime 102367 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_102677 : Nat.Prime 102677 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_105967 : Nat.Prime 105967 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_108041 : Nat.Prime 108041 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_108503 : Nat.Prime 108503 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_110581 : Nat.Prime 110581 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_111863 : Nat.Prime 111863 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_112199 : Nat.Prime 112199 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_116833 : Nat.Prime 116833 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_120299 : Nat.Prime 120299 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_121007 : Nat.Prime 121007 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_125149 : Nat.Prime 125149 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_127873 : Nat.Prime 127873 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_133831 : Nat.Prime 133831 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_138371 : Nat.Prime 138371 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_140837 : Nat.Prime 140837 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_141107 : Nat.Prime 141107 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_146519 : Nat.Prime 146519 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_148201 : Nat.Prime 148201 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_158993 : Nat.Prime 158993 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_162823 : Nat.Prime 162823 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_170239 : Nat.Prime 170239 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_170669 : Nat.Prime 170669 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_174599 : Nat.Prime 174599 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_179051 : Nat.Prime 179051 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_183709 : Nat.Prime 183709 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_192791 : Nat.Prime 192791 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_205949 : Nat.Prime 205949 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_207401 : Nat.Prime 207401 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_207661 : Nat.Prime 207661 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_211927 : Nat.Prime 211927 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_237409 : Nat.Prime 237409 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_242453 : Nat.Prime 242453 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_242789 : Nat.Prime 242789 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_247067 : Nat.Prime 247067 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_255977 : Nat.Prime 255977 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_257903 : Nat.Prime 257903 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_263843 : Nat.Prime 263843 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_299087 : Nat.Prime 299087 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_302573 : Nat.Prime 302573 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_305947 : Nat.Prime 305947 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_410243 : Nat.Prime 410243 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_496919 : Nat.Prime 496919 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_500777 : Nat.Prime 500777 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_503647 : Nat.Prime 503647 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_537781 : Nat.Prime 537781 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_563837 : Nat.Prime 563837 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_563999 : Nat.Prime 563999 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_581137 : Nat.Prime 581137 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_586387 : Nat.Prime 586387 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_630871 : Nat.Prime 630871 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_639637 : Nat.Prime 639637 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_649183 : Nat.Prime 649183 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_649799 : Nat.Prime 649799 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_688637 : Nat.Prime 688637 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_697033 : Nat.Prime 697033 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_716743 : Nat.Prime 716743 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_749779 : Nat.Prime 749779 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_872017 : Nat.Prime 872017 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_910207 : Nat.Prime 910207 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_925943 : Nat.Prime 925943 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_935461 : Nat.Prime 935461 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_960017 : Nat.Prime 960017 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1053953 : Nat.Prime 1053953 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1102861 : Nat.Prime 1102861 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1141243 : Nat.Prime 1141243 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1163609 : Nat.Prime 1163609 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1164659 : Nat.Prime 1164659 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1203733 : Nat.Prime 1203733 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1275121 : Nat.Prime 1275121 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1406479 : Nat.Prime 1406479 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1467043 : Nat.Prime 1467043 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1469521 : Nat.Prime 1469521 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1513361 : Nat.Prime 1513361 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1705009 : Nat.Prime 1705009 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1726561 : Nat.Prime 1726561 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1880647 : Nat.Prime 1880647 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1984013 : Nat.Prime 1984013 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_1986167 : Nat.Prime 1986167 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2080027 : Nat.Prime 2080027 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2109979 : Nat.Prime 2109979 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2256341 : Nat.Prime 2256341 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2314759 : Nat.Prime 2314759 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2350891 : Nat.Prime 2350891 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2375761 : Nat.Prime 2375761 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2432987 : Nat.Prime 2432987 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2526967 : Nat.Prime 2526967 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2618741 : Nat.Prime 2618741 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2755793 : Nat.Prime 2755793 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_2878679 : Nat.Prime 2878679 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3026183 : Nat.Prime 3026183 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3126377 : Nat.Prime 3126377 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3507113 : Nat.Prime 3507113 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_3608249 : Nat.Prime 3608249 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4025089 : Nat.Prime 4025089 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4044289 : Nat.Prime 4044289 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4045357 : Nat.Prime 4045357 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4070483 : Nat.Prime 4070483 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4181509 : Nat.Prime 4181509 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_4815817 : Nat.Prime 4815817 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5008417 : Nat.Prime 5008417 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5053897 : Nat.Prime 5053897 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_5128987 : Nat.Prime 5128987 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_6130667 : Nat.Prime 6130667 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_6959677 : Nat.Prime 6959677 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7086169 : Nat.Prime 7086169 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7114817 : Nat.Prime 7114817 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7210169 : Nat.Prime 7210169 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_7288399 : Nat.Prime 7288399 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8154473 : Nat.Prime 8154473 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8227591 : Nat.Prime 8227591 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8359679 : Nat.Prime 8359679 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_8596901 : Nat.Prime 8596901 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_9229177 : Nat.Prime 9229177 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_9910073 : Nat.Prime 9910073 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_10376309 : Nat.Prime 10376309 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_10924399 : Nat.Prime 10924399 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_11246699 : Nat.Prime 11246699 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_11339213 : Nat.Prime 11339213 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_11539069 : Nat.Prime 11539069 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_11703161 : Nat.Prime 11703161 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_13607551 : Nat.Prime 13607551 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_13849159 : Nat.Prime 13849159 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_14860841 : Nat.Prime 14860841 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_15803939 : Nat.Prime 15803939 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_16981813 : Nat.Prime 16981813 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_17160961 : Nat.Prime 17160961 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_17326697 : Nat.Prime 17326697 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_20332297 : Nat.Prime 20332297 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_20897759 : Nat.Prime 20897759 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_21349571 : Nat.Prime 21349571 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_22269943 : Nat.Prime 22269943 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_23474587 : Nat.Prime 23474587 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_24729857 : Nat.Prime 24729857 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_26709367 : Nat.Prime 26709367 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_27271141 : Nat.Prime 27271141 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_27730687 : Nat.Prime 27730687 := by norm_num

private theorem prime_oneHundredTwentyTwoDP_30695257 : Nat.Prime 30695257 := by
  apply lucas_primality 30695257 (5 : ZMod 30695257)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (263, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (263, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) = 30695257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_263
      · exact prime_oneHundredTwentyTwoDP_1621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 30695257) ^ 15347628 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30695257) ^ 10231752 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30695257) ^ 116712 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30695257) ^ 18936 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_32388457 : Nat.Prime 32388457 := by
  apply lucas_primality 32388457 (5 : ZMod 32388457)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (353, 1), (3823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (353, 1), (3823, 1)] : List FactorBlock).map factorBlockValue).prod) = 32388457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_353
      · exact prime_oneHundredTwentyTwoDP_3823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32388457) ^ 16194228 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32388457) ^ 10796152 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32388457) ^ 91752 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 32388457) ^ 8472 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_33800159 : Nat.Prime 33800159 := by
  apply lucas_primality 33800159 (7 : ZMod 33800159)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1289, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1289, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) = 33800159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_1289
      · exact prime_oneHundredTwentyTwoDP_1873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 33800159) ^ 16900079 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 33800159) ^ 4828594 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 33800159) ^ 26222 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 33800159) ^ 18046 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_34999507 : Nat.Prime 34999507 := by
  apply lucas_primality 34999507 (7 : ZMod 34999507)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (43, 1), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (43, 1), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) = 34999507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_43
      · exact prime_oneHundredTwentyTwoDP_15073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 34999507) ^ 17499753 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 34999507) ^ 11666502 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 34999507) ^ 813942 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 34999507) ^ 2322 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_38104529 : Nat.Prime 38104529 := by
  apply lucas_primality 38104529 (3 : ZMod 38104529)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (157, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (157, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod) = 38104529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_157
      · exact prime_oneHundredTwentyTwoDP_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38104529) ^ 19052264 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 38104529) ^ 5443504 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 38104529) ^ 3464048 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 38104529) ^ 242704 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 38104529) ^ 193424 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_38956417 : Nat.Prime 38956417 := by
  apply lucas_primality 38956417 (7 : ZMod 38956417)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (101449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (101449, 1)] : List FactorBlock).map factorBlockValue).prod) = 38956417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_101449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 38956417) ^ 19478208 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 38956417) ^ 12985472 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 38956417) ^ 384 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_40431473 : Nat.Prime 40431473 := by
  apply lucas_primality 40431473 (3 : ZMod 40431473)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2526967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2526967, 1)] : List FactorBlock).map factorBlockValue).prod) = 40431473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_2526967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 40431473) ^ 20215736 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 40431473) ^ 16 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_41084749 : Nat.Prime 41084749 := by
  apply lucas_primality 41084749 (2 : ZMod 41084749)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1141243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1141243, 1)] : List FactorBlock).map factorBlockValue).prod) = 41084749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_1141243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41084749) ^ 20542374 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 41084749) ^ 13694916 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 41084749) ^ 36 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_41758063 : Nat.Prime 41758063 := by
  apply lucas_primality 41758063 (3 : ZMod 41758063)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6959677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6959677, 1)] : List FactorBlock).map factorBlockValue).prod) = 41758063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_6959677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41758063) ^ 20879031 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41758063) ^ 13919354 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41758063) ^ 6 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_42128641 : Nat.Prime 42128641 := by
  apply lucas_primality 42128641 (31 : ZMod 42128641)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 1), (23, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 1), (23, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod) = 42128641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_23
      · exact prime_oneHundredTwentyTwoDP_53
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 42128641) ^ 21064320 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (31 : ZMod 42128641) ^ 14042880 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (31 : ZMod 42128641) ^ 8425728 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (31 : ZMod 42128641) ^ 1831680 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (31 : ZMod 42128641) ^ 794880 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_43326037 : Nat.Prime 43326037 := by
  apply lucas_primality 43326037 (2 : ZMod 43326037)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (30859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (30859, 1)] : List FactorBlock).map factorBlockValue).prod) = 43326037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_30859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43326037) ^ 21663018 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 43326037) ^ 14442012 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 43326037) ^ 3332772 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 43326037) ^ 1404 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_43697597 : Nat.Prime 43697597 := by
  apply lucas_primality 43697597 (2 : ZMod 43697597)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10924399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10924399, 1)] : List FactorBlock).map factorBlockValue).prod) = 43697597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_10924399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 43697597) ^ 21848798 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 43697597) ^ 4 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_51289871 : Nat.Prime 51289871 := by
  apply lucas_primality 51289871 (19 : ZMod 51289871)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5128987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5128987, 1)] : List FactorBlock).map factorBlockValue).prod) = 51289871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_5128987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 51289871) ^ 25644935 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 51289871) ^ 10257974 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 51289871) ^ 10 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_52565179 : Nat.Prime 52565179 := by
  apply lucas_primality 52565179 (3 : ZMod 52565179)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (79, 1), (2579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (79, 1), (2579, 1)] : List FactorBlock).map factorBlockValue).prod) = 52565179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_43
      · exact prime_oneHundredTwentyTwoDP_79
      · exact prime_oneHundredTwentyTwoDP_2579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52565179) ^ 26282589 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52565179) ^ 17521726 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52565179) ^ 1222446 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52565179) ^ 665382 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52565179) ^ 20382 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_1811
      · exact prime_oneHundredTwentyTwoDP_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_60442721 : Nat.Prime 60442721 := by
  apply lucas_primality 60442721 (6 : ZMod 60442721)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 1), (29059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 1), (29059, 1)] : List FactorBlock).map factorBlockValue).prod) = 60442721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_29059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 60442721) ^ 30221360 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 60442721) ^ 12088544 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 60442721) ^ 4649440 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 60442721) ^ 2080 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_60593479 : Nat.Prime 60593479 := by
  apply lucas_primality 60593479 (6 : ZMod 60593479)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (127, 1), (7229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (127, 1), (7229, 1)] : List FactorBlock).map factorBlockValue).prod) = 60593479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_127
      · exact prime_oneHundredTwentyTwoDP_7229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 60593479) ^ 30296739 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 60593479) ^ 20197826 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 60593479) ^ 5508498 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 60593479) ^ 477114 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 60593479) ^ 8382 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_63459523 : Nat.Prime 63459523 := by
  apply lucas_primality 63459523 (2 : ZMod 63459523)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (503647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (503647, 1)] : List FactorBlock).map factorBlockValue).prod) = 63459523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_503647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63459523) ^ 31729761 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63459523) ^ 21153174 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63459523) ^ 9065646 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63459523) ^ 126 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_67121893 : Nat.Prime 67121893 := by
  apply lucas_primality 67121893 (6 : ZMod 67121893)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (29, 2), (739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (29, 2), (739, 1)] : List FactorBlock).map factorBlockValue).prod) = 67121893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_29
      · exact prime_oneHundredTwentyTwoDP_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 67121893) ^ 33560946 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 67121893) ^ 22373964 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 67121893) ^ 2314548 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 67121893) ^ 90828 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_70146781 : Nat.Prime 70146781 := by
  apply lucas_primality 70146781 (7 : ZMod 70146781)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (4621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (4621, 1)] : List FactorBlock).map factorBlockValue).prod) = 70146781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_23
      · exact prime_oneHundredTwentyTwoDP_4621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 70146781) ^ 35073390 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 70146781) ^ 23382260 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 70146781) ^ 14029356 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 70146781) ^ 6376980 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 70146781) ^ 3049860 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 70146781) ^ 15180 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_75043427 : Nat.Prime 75043427 := by
  apply lucas_primality 75043427 (2 : ZMod 75043427)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (367, 1), (5381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (367, 1), (5381, 1)] : List FactorBlock).map factorBlockValue).prod) = 75043427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_367
      · exact prime_oneHundredTwentyTwoDP_5381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75043427) ^ 37521713 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 75043427) ^ 3949654 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 75043427) ^ 204478 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 75043427) ^ 13946 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_76480009 : Nat.Prime 76480009 := by
  apply lucas_primality 76480009 (13 : ZMod 76480009)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (17, 1), (17041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (17, 1), (17041, 1)] : List FactorBlock).map factorBlockValue).prod) = 76480009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_17041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 76480009) ^ 38240004 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 76480009) ^ 25493336 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 76480009) ^ 6952728 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 76480009) ^ 4498824 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 76480009) ^ 4488 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_88651943 : Nat.Prime 88651943 := by
  apply lucas_primality 88651943 (5 : ZMod 88651943)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (619, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (619, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod) = 88651943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_101
      · exact prime_oneHundredTwentyTwoDP_619
      · exact prime_oneHundredTwentyTwoDP_709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 88651943) ^ 44325971 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 88651943) ^ 877742 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 88651943) ^ 143218 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 88651943) ^ 125038 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_93420773 : Nat.Prime 93420773 := by
  apply lucas_primality 93420773 (2 : ZMod 93420773)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (496919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (496919, 1)] : List FactorBlock).map factorBlockValue).prod) = 93420773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_47
      · exact prime_oneHundredTwentyTwoDP_496919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93420773) ^ 46710386 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93420773) ^ 1987676 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93420773) ^ 188 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_95363383 : Nat.Prime 95363383 := by
  apply lucas_primality 95363383 (3 : ZMod 95363383)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (461, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (461, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) = 95363383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_23
      · exact prime_oneHundredTwentyTwoDP_461
      · exact prime_oneHundredTwentyTwoDP_1499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95363383) ^ 47681691 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 95363383) ^ 31787794 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 95363383) ^ 4146234 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 95363383) ^ 206862 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 95363383) ^ 63618 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_104661989 : Nat.Prime 104661989 := by
  apply lucas_primality 104661989 (2 : ZMod 104661989)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (317, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (317, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 104661989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_59
      · exact prime_oneHundredTwentyTwoDP_317
      · exact prime_oneHundredTwentyTwoDP_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104661989) ^ 52330994 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104661989) ^ 1773932 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104661989) ^ 330164 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 104661989) ^ 74812 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_105200659 : Nat.Prime 105200659 := by
  apply lucas_primality 105200659 (2 : ZMod 105200659)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (59, 1), (5827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (59, 1), (5827, 1)] : List FactorBlock).map factorBlockValue).prod) = 105200659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_59
      · exact prime_oneHundredTwentyTwoDP_5827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105200659) ^ 52600329 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 105200659) ^ 35066886 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 105200659) ^ 6188274 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 105200659) ^ 1783062 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 105200659) ^ 18054 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_116864299 : Nat.Prime 116864299 := by
  apply lucas_primality 116864299 (2 : ZMod 116864299)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (89, 1), (72949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (89, 1), (72949, 1)] : List FactorBlock).map factorBlockValue).prod) = 116864299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_89
      · exact prime_oneHundredTwentyTwoDP_72949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 116864299) ^ 58432149 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 116864299) ^ 38954766 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 116864299) ^ 1313082 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 116864299) ^ 1602 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_141680531 : Nat.Prime 141680531 := by
  apply lucas_primality 141680531 (2 : ZMod 141680531)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (113, 1), (6599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (113, 1), (6599, 1)] : List FactorBlock).map factorBlockValue).prod) = 141680531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_113
      · exact prime_oneHundredTwentyTwoDP_6599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141680531) ^ 70840265 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 141680531) ^ 28336106 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 141680531) ^ 7456870 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 141680531) ^ 1253810 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 141680531) ^ 21470 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_148566191 : Nat.Prime 148566191 := by
  apply lucas_primality 148566191 (7 : ZMod 148566191)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (619, 1), (24001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (619, 1), (24001, 1)] : List FactorBlock).map factorBlockValue).prod) = 148566191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_619
      · exact prime_oneHundredTwentyTwoDP_24001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 148566191) ^ 74283095 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 148566191) ^ 29713238 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 148566191) ^ 240010 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 148566191) ^ 6190 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_149846629 : Nat.Prime 149846629 := by
  apply lucas_primality 149846629 (2 : ZMod 149846629)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (69761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (69761, 1)] : List FactorBlock).map factorBlockValue).prod) = 149846629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_179
      · exact prime_oneHundredTwentyTwoDP_69761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 149846629) ^ 74923314 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 149846629) ^ 49948876 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 149846629) ^ 837132 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 149846629) ^ 2148 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_158137079 : Nat.Prime 158137079 := by
  apply lucas_primality 158137079 (7 : ZMod 158137079)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (83, 1), (7873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (83, 1), (7873, 1)] : List FactorBlock).map factorBlockValue).prod) = 158137079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_83
      · exact prime_oneHundredTwentyTwoDP_7873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 158137079) ^ 79068539 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 158137079) ^ 14376098 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 158137079) ^ 1905266 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 158137079) ^ 20086 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_168047101 : Nat.Prime 168047101 := by
  apply lucas_primality 168047101 (6 : ZMod 168047101)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (13, 1), (53, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (13, 1), (53, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) = 168047101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_53
      · exact prime_oneHundredTwentyTwoDP_271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 168047101) ^ 84023550 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 168047101) ^ 56015700 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 168047101) ^ 33609420 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 168047101) ^ 12926700 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 168047101) ^ 3170700 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 168047101) ^ 620100 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_181755421 : Nat.Prime 181755421 := by
  apply lucas_primality 181755421 (6 : ZMod 181755421)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (39341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (39341, 1)] : List FactorBlock).map factorBlockValue).prod) = 181755421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_39341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 181755421) ^ 90877710 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 181755421) ^ 60585140 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 181755421) ^ 36351084 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 181755421) ^ 25965060 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 181755421) ^ 16523220 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 181755421) ^ 4620 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_212512073 : Nat.Prime 212512073 := by
  apply lucas_primality 212512073 (3 : ZMod 212512073)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (257903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (257903, 1)] : List FactorBlock).map factorBlockValue).prod) = 212512073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_103
      · exact prime_oneHundredTwentyTwoDP_257903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 212512073) ^ 106256036 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212512073) ^ 2063224 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 212512073) ^ 824 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_227534897 : Nat.Prime 227534897 := by
  apply lucas_primality 227534897 (3 : ZMod 227534897)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (47, 1), (302573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (47, 1), (302573, 1)] : List FactorBlock).map factorBlockValue).prod) = 227534897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_47
      · exact prime_oneHundredTwentyTwoDP_302573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 227534897) ^ 113767448 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 227534897) ^ 4841168 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 227534897) ^ 752 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_227849599 : Nat.Prime 227849599 := by
  apply lucas_primality 227849599 (3 : ZMod 227849599)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1406479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1406479, 1)] : List FactorBlock).map factorBlockValue).prod) = 227849599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_1406479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 227849599) ^ 113924799 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 227849599) ^ 75949866 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 227849599) ^ 162 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_258134881 : Nat.Prime 258134881 := by
  apply lucas_primality 258134881 (37 : ZMod 258134881)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (537781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (537781, 1)] : List FactorBlock).map factorBlockValue).prod) = 258134881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_537781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (37 : ZMod 258134881) ^ 129067440 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (37 : ZMod 258134881) ^ 86044960 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (37 : ZMod 258134881) ^ 51626976 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (37 : ZMod 258134881) ^ 480 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_289429997 : Nat.Prime 289429997 := by
  apply lucas_primality 289429997 (2 : ZMod 289429997)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2969, 1), (24371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2969, 1), (24371, 1)] : List FactorBlock).map factorBlockValue).prod) = 289429997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_2969
      · exact prime_oneHundredTwentyTwoDP_24371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 289429997) ^ 144714998 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 289429997) ^ 97484 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 289429997) ^ 11876 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_307739227 : Nat.Prime 307739227 := by
  apply lucas_primality 307739227 (2 : ZMod 307739227)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (51289871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (51289871, 1)] : List FactorBlock).map factorBlockValue).prod) = 307739227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_51289871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 307739227) ^ 153869613 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 307739227) ^ 102579742 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 307739227) ^ 6 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_342175879 : Nat.Prime 342175879 := by
  apply lucas_primality 342175879 (3 : ZMod 342175879)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (233, 1), (7417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (233, 1), (7417, 1)] : List FactorBlock).map factorBlockValue).prod) = 342175879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_233
      · exact prime_oneHundredTwentyTwoDP_7417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 342175879) ^ 171087939 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 342175879) ^ 114058626 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 342175879) ^ 31106898 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 342175879) ^ 1468566 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 342175879) ^ 46134 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_346217999 : Nat.Prime 346217999 := by
  apply lucas_primality 346217999 (7 : ZMod 346217999)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (24729857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (24729857, 1)] : List FactorBlock).map factorBlockValue).prod) = 346217999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_24729857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 346217999) ^ 173108999 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 346217999) ^ 49459714 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 346217999) ^ 14 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_370223857 : Nat.Prime 370223857 := by
  apply lucas_primality 370223857 (5 : ZMod 370223857)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (163, 1), (15773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (163, 1), (15773, 1)] : List FactorBlock).map factorBlockValue).prod) = 370223857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_163
      · exact prime_oneHundredTwentyTwoDP_15773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 370223857) ^ 185111928 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 370223857) ^ 123407952 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 370223857) ^ 2271312 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 370223857) ^ 23472 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_374119237 : Nat.Prime 374119237 := by
  apply lucas_primality 374119237 (2 : ZMod 374119237)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (59, 1), (19571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (59, 1), (19571, 1)] : List FactorBlock).map factorBlockValue).prod) = 374119237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_59
      · exact prime_oneHundredTwentyTwoDP_19571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 374119237) ^ 187059618 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 374119237) ^ 124706412 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 374119237) ^ 6341004 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 374119237) ^ 19116 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_414995297 : Nat.Prime 414995297 := by
  apply lucas_primality 414995297 (3 : ZMod 414995297)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (719, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (719, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) = 414995297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_719
      · exact prime_oneHundredTwentyTwoDP_1061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 414995297) ^ 207497648 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 414995297) ^ 24411488 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 414995297) ^ 577184 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 414995297) ^ 391136 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_500316319 : Nat.Prime 500316319 := by
  apply lucas_primality 500316319 (3 : ZMod 500316319)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (701, 1), (13217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (701, 1), (13217, 1)] : List FactorBlock).map factorBlockValue).prod) = 500316319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_701
      · exact prime_oneHundredTwentyTwoDP_13217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 500316319) ^ 250158159 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 500316319) ^ 166772106 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 500316319) ^ 713718 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 500316319) ^ 37854 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_540907229 : Nat.Prime 540907229 := by
  apply lucas_primality 540907229 (2 : ZMod 540907229)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1321, 1), (102367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1321, 1), (102367, 1)] : List FactorBlock).map factorBlockValue).prod) = 540907229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_1321
      · exact prime_oneHundredTwentyTwoDP_102367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 540907229) ^ 270453614 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 540907229) ^ 409468 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 540907229) ^ 5284 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_550247627 : Nat.Prime 550247627 := by
  apply lucas_primality 550247627 (2 : ZMod 550247627)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (120299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (120299, 1)] : List FactorBlock).map factorBlockValue).prod) = 550247627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_2287
      · exact prime_oneHundredTwentyTwoDP_120299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 550247627) ^ 275123813 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 550247627) ^ 240598 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 550247627) ^ 4574 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_560524639 : Nat.Prime 560524639 := by
  apply lucas_primality 560524639 (3 : ZMod 560524639)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (93420773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (93420773, 1)] : List FactorBlock).map factorBlockValue).prod) = 560524639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_93420773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 560524639) ^ 280262319 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 560524639) ^ 186841546 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 560524639) ^ 6 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_599386517 : Nat.Prime 599386517 := by
  apply lucas_primality 599386517 (2 : ZMod 599386517)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149846629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149846629, 1)] : List FactorBlock).map factorBlockValue).prod) = 599386517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_149846629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 599386517) ^ 299693258 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 599386517) ^ 4 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_607248751 : Nat.Prime 607248751 := by
  apply lucas_primality 607248751 (6 : ZMod 607248751)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (83, 1), (1951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (83, 1), (1951, 1)] : List FactorBlock).map factorBlockValue).prod) = 607248751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_83
      · exact prime_oneHundredTwentyTwoDP_1951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 607248751) ^ 303624375 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 607248751) ^ 202416250 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 607248751) ^ 121449750 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 607248751) ^ 7316250 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 607248751) ^ 311250 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_662034467 : Nat.Prime 662034467 := by
  apply lucas_primality 662034467 (2 : ZMod 662034467)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (1657, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (1657, 1), (1867, 1)] : List FactorBlock).map factorBlockValue).prod) = 662034467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_107
      · exact prime_oneHundredTwentyTwoDP_1657
      · exact prime_oneHundredTwentyTwoDP_1867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 662034467) ^ 331017233 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 662034467) ^ 6187238 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 662034467) ^ 399538 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 662034467) ^ 354598 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_688816129 : Nat.Prime 688816129 := by
  apply lucas_primality 688816129 (47 : ZMod 688816129)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 15), (3, 1), (7, 2), (11, 1), (13, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 15), (3, 1), (7, 2), (11, 1), (13, 1)] : List FactorBlock).map factorBlockValue).prod) = 688816129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_13
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (47 : ZMod 688816129) ^ 344408064 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (47 : ZMod 688816129) ^ 229605376 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (47 : ZMod 688816129) ^ 98402304 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (47 : ZMod 688816129) ^ 62619648 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (47 : ZMod 688816129) ^ 52985856 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_701101669 : Nat.Prime 701101669 := by
  apply lucas_primality 701101669 (2 : ZMod 701101669)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (872017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (872017, 1)] : List FactorBlock).map factorBlockValue).prod) = 701101669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_67
      · exact prime_oneHundredTwentyTwoDP_872017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 701101669) ^ 350550834 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 701101669) ^ 233700556 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 701101669) ^ 10464204 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 701101669) ^ 804 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_17203
      · exact prime_oneHundredTwentyTwoDP_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_817390601 : Nat.Prime 817390601 := by
  apply lucas_primality 817390601 (7 : ZMod 817390601)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (17, 1), (18493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (17, 1), (18493, 1)] : List FactorBlock).map factorBlockValue).prod) = 817390601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_18493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 817390601) ^ 408695300 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 817390601) ^ 163478120 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 817390601) ^ 62876200 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 817390601) ^ 48081800 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 817390601) ^ 44200 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_818684509 : Nat.Prime 818684509 := by
  apply lucas_primality 818684509 (6 : ZMod 818684509)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (281, 1), (242789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (281, 1), (242789, 1)] : List FactorBlock).map factorBlockValue).prod) = 818684509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_281
      · exact prime_oneHundredTwentyTwoDP_242789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 818684509) ^ 409342254 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 818684509) ^ 272894836 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 818684509) ^ 2913468 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 818684509) ^ 3372 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_834881737 : Nat.Prime 834881737 := by
  apply lucas_primality 834881737 (15 : ZMod 834881737)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (140837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (140837, 1)] : List FactorBlock).map factorBlockValue).prod) = 834881737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_140837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 834881737) ^ 417440868 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (15 : ZMod 834881737) ^ 278293912 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (15 : ZMod 834881737) ^ 64221672 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (15 : ZMod 834881737) ^ 43941144 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (15 : ZMod 834881737) ^ 5928 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1023310333 : Nat.Prime 1023310333 := by
  apply lucas_primality 1023310333 (5 : ZMod 1023310333)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (37, 1), (211, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (37, 1), (211, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 1023310333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_37
      · exact prime_oneHundredTwentyTwoDP_211
      · exact prime_oneHundredTwentyTwoDP_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1023310333) ^ 511655166 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1023310333) ^ 341103444 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1023310333) ^ 93028212 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1023310333) ^ 27657036 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1023310333) ^ 4849812 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1023310333) ^ 3091572 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1039622813 : Nat.Prime 1039622813 := by
  apply lucas_primality 1039622813 (2 : ZMod 1039622813)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (1984013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (1984013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1039622813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_131
      · exact prime_oneHundredTwentyTwoDP_1984013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1039622813) ^ 519811406 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039622813) ^ 7936052 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039622813) ^ 524 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1157156879 : Nat.Prime 1157156879 := by
  apply lucas_primality 1157156879 (7 : ZMod 1157156879)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (401, 1), (607, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (401, 1), (607, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157156879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_401
      · exact prime_oneHundredTwentyTwoDP_607
      · exact prime_oneHundredTwentyTwoDP_2377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1157156879) ^ 578578439 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1157156879) ^ 2885678 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1157156879) ^ 1906354 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1157156879) ^ 486814 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1409428039 : Nat.Prime 1409428039 := by
  apply lucas_primality 1409428039 (3 : ZMod 1409428039)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1877, 1), (125149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1877, 1), (125149, 1)] : List FactorBlock).map factorBlockValue).prod) = 1409428039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_1877
      · exact prime_oneHundredTwentyTwoDP_125149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1409428039) ^ 704714019 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409428039) ^ 469809346 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409428039) ^ 750894 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409428039) ^ 11262 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1422126751 : Nat.Prime 1422126751 := by
  apply lucas_primality 1422126751 (13 : ZMod 1422126751)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (11, 1), (223, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (11, 1), (223, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1422126751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_223
      · exact prime_oneHundredTwentyTwoDP_773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1422126751) ^ 711063375 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1422126751) ^ 474042250 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1422126751) ^ 284425350 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1422126751) ^ 129284250 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1422126751) ^ 6377250 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1422126751) ^ 1839750 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2021573651 : Nat.Prime 2021573651 := by
  apply lucas_primality 2021573651 (2 : ZMod 2021573651)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (40431473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (40431473, 1)] : List FactorBlock).map factorBlockValue).prod) = 2021573651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_40431473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2021573651) ^ 1010786825 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2021573651) ^ 404314730 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2021573651) ^ 50 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2187499637 : Nat.Prime 2187499637 := by
  apply lucas_primality 2187499637 (2 : ZMod 2187499637)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (109, 1), (716743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (109, 1), (716743, 1)] : List FactorBlock).map factorBlockValue).prod) = 2187499637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_109
      · exact prime_oneHundredTwentyTwoDP_716743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2187499637) ^ 1093749818 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2187499637) ^ 312499948 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2187499637) ^ 20068804 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2187499637) ^ 3052 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2381625691 : Nat.Prime 2381625691 := by
  apply lucas_primality 2381625691 (11 : ZMod 2381625691)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2113, 1), (37571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2113, 1), (37571, 1)] : List FactorBlock).map factorBlockValue).prod) = 2381625691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_2113
      · exact prime_oneHundredTwentyTwoDP_37571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2381625691) ^ 1190812845 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2381625691) ^ 793875230 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2381625691) ^ 476325138 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2381625691) ^ 1127130 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2381625691) ^ 63390 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2856675119 : Nat.Prime 2856675119 := by
  apply lucas_primality 2856675119 (7 : ZMod 2856675119)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (23, 2), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (23, 2), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2856675119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_23
      · exact prime_oneHundredTwentyTwoDP_12919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2856675119) ^ 1428337559 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2856675119) ^ 259697738 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2856675119) ^ 150351322 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2856675119) ^ 124203266 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2856675119) ^ 221122 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3112892701 : Nat.Prime 3112892701 := by
  apply lucas_primality 3112892701 (10 : ZMod 3112892701)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (10376309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (10376309, 1)] : List FactorBlock).map factorBlockValue).prod) = 3112892701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_10376309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 3112892701) ^ 1556446350 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3112892701) ^ 1037630900 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3112892701) ^ 622578540 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3112892701) ^ 300 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3357435409 : Nat.Prime 3357435409 := by
  apply lucas_primality 3357435409 (14 : ZMod 3357435409)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (2256341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (2256341, 1)] : List FactorBlock).map factorBlockValue).prod) = 3357435409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_2256341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 3357435409) ^ 1678717704 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (14 : ZMod 3357435409) ^ 1119145136 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (14 : ZMod 3357435409) ^ 108304368 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (14 : ZMod 3357435409) ^ 1488 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3389304553 : Nat.Prime 3389304553 := by
  apply lucas_primality 3389304553 (7 : ZMod 3389304553)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (1579, 1), (5261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (1579, 1), (5261, 1)] : List FactorBlock).map factorBlockValue).prod) = 3389304553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_1579
      · exact prime_oneHundredTwentyTwoDP_5261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3389304553) ^ 1694652276 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3389304553) ^ 1129768184 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3389304553) ^ 199370856 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3389304553) ^ 2146488 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3389304553) ^ 644232 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3443628619 : Nat.Prime 3443628619 := by
  apply lucas_primality 3443628619 (7 : ZMod 3443628619)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (4070483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (4070483, 1)] : List FactorBlock).map factorBlockValue).prod) = 3443628619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_47
      · exact prime_oneHundredTwentyTwoDP_4070483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3443628619) ^ 1721814309 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3443628619) ^ 1147876206 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3443628619) ^ 73268694 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3443628619) ^ 846 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3951328393 : Nat.Prime 3951328393 := by
  apply lucas_primality 3951328393 (5 : ZMod 3951328393)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (11, 1), (491, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (11, 1), (491, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) = 3951328393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_491
      · exact prime_oneHundredTwentyTwoDP_1129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3951328393) ^ 1975664196 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951328393) ^ 1317109464 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951328393) ^ 359211672 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951328393) ^ 8047512 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951328393) ^ 3499848 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_4239579373 : Nat.Prime 4239579373 := by
  apply lucas_primality 4239579373 (2 : ZMod 4239579373)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (7210169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (7210169, 1)] : List FactorBlock).map factorBlockValue).prod) = 4239579373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_7210169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4239579373) ^ 2119789686 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4239579373) ^ 1413193124 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4239579373) ^ 605654196 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4239579373) ^ 588 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_4455095321 : Nat.Prime 4455095321 := by
  apply lucas_primality 4455095321 (3 : ZMod 4455095321)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (67, 1), (127873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (67, 1), (127873, 1)] : List FactorBlock).map factorBlockValue).prod) = 4455095321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_67
      · exact prime_oneHundredTwentyTwoDP_127873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4455095321) ^ 2227547660 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4455095321) ^ 891019064 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4455095321) ^ 342699640 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4455095321) ^ 66493960 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4455095321) ^ 34840 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_5149622683 : Nat.Prime 5149622683 := by
  apply lucas_primality 5149622683 (2 : ZMod 5149622683)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (95363383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (95363383, 1)] : List FactorBlock).map factorBlockValue).prod) = 5149622683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_95363383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5149622683) ^ 2574811341 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5149622683) ^ 1716540894 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5149622683) ^ 54 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_5468390377 : Nat.Prime 5468390377 := by
  apply lucas_primality 5468390377 (5 : ZMod 5468390377)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (227849599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (227849599, 1)] : List FactorBlock).map factorBlockValue).prod) = 5468390377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_227849599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5468390377) ^ 2734195188 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5468390377) ^ 1822796792 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5468390377) ^ 24 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_5484538481 : Nat.Prime 5484538481 := by
  apply lucas_primality 5484538481 (3 : ZMod 5484538481)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (19, 1), (3608249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (19, 1), (3608249, 1)] : List FactorBlock).map factorBlockValue).prod) = 5484538481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_3608249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5484538481) ^ 2742269240 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5484538481) ^ 1096907696 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5484538481) ^ 288659920 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5484538481) ^ 1520 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_6072487511 : Nat.Prime 6072487511 := by
  apply lucas_primality 6072487511 (17 : ZMod 6072487511)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (607248751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (607248751, 1)] : List FactorBlock).map factorBlockValue).prod) = 6072487511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_607248751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 6072487511) ^ 3036243755 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 6072487511) ^ 1214497502 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 6072487511) ^ 10 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_6510166489 : Nat.Prime 6510166489 := by
  apply lucas_primality 6510166489 (13 : ZMod 6510166489)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (67, 1), (192791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (67, 1), (192791, 1)] : List FactorBlock).map factorBlockValue).prod) = 6510166489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_67
      · exact prime_oneHundredTwentyTwoDP_192791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6510166489) ^ 3255083244 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 6510166489) ^ 2170055496 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 6510166489) ^ 930023784 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 6510166489) ^ 97166664 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 6510166489) ^ 33768 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_7693661881 : Nat.Prime 7693661881 := by
  apply lucas_primality 7693661881 (7 : ZMod 7693661881)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 6), (5, 1), (263843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 6), (5, 1), (263843, 1)] : List FactorBlock).map factorBlockValue).prod) = 7693661881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_263843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7693661881) ^ 3846830940 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 7693661881) ^ 2564553960 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 7693661881) ^ 1538732376 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 7693661881) ^ 29160 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_8299119299 : Nat.Prime 8299119299 := by
  apply lucas_primality 8299119299 (2 : ZMod 8299119299)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (41084749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (41084749, 1)] : List FactorBlock).map factorBlockValue).prod) = 8299119299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_101
      · exact prime_oneHundredTwentyTwoDP_41084749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8299119299) ^ 4149559649 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8299119299) ^ 82169498 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8299119299) ^ 202 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_8596111529 : Nat.Prime 8596111529 := by
  apply lucas_primality 8596111529 (3 : ZMod 8596111529)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5849, 1), (183709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5849, 1), (183709, 1)] : List FactorBlock).map factorBlockValue).prod) = 8596111529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5849
      · exact prime_oneHundredTwentyTwoDP_183709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8596111529) ^ 4298055764 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8596111529) ^ 1469672 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8596111529) ^ 46792 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_8984742589 : Nat.Prime 8984742589 := by
  apply lucas_primality 8984742589 (2 : ZMod 8984742589)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (27730687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (27730687, 1)] : List FactorBlock).map factorBlockValue).prod) = 8984742589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_27730687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8984742589) ^ 4492371294 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8984742589) ^ 2994914196 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8984742589) ^ 324 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_9057356501 : Nat.Prime 9057356501 := by
  apply lucas_primality 9057356501 (2 : ZMod 9057356501)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (103, 1), (397, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (103, 1), (397, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 9057356501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_103
      · exact prime_oneHundredTwentyTwoDP_397
      · exact prime_oneHundredTwentyTwoDP_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9057356501) ^ 4528678250 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9057356501) ^ 1811471300 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9057356501) ^ 87935500 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9057356501) ^ 22814500 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9057356501) ^ 20445500 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_9444288671 : Nat.Prime 9444288671 := by
  apply lucas_primality 9444288671 (11 : ZMod 9444288671)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (547, 1), (1726561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (547, 1), (1726561, 1)] : List FactorBlock).map factorBlockValue).prod) = 9444288671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_547
      · exact prime_oneHundredTwentyTwoDP_1726561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 9444288671) ^ 4722144335 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 9444288671) ^ 1888857734 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 9444288671) ^ 17265610 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 9444288671) ^ 5470 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_9904457287 : Nat.Prime 9904457287 := by
  apply lucas_primality 9904457287 (3 : ZMod 9904457287)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (550247627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (550247627, 1)] : List FactorBlock).map factorBlockValue).prod) = 9904457287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_550247627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9904457287) ^ 4952228643 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9904457287) ^ 3301485762 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9904457287) ^ 18 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_11124129287 : Nat.Prime 11124129287 := by
  apply lucas_primality 11124129287 (5 : ZMod 11124129287)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (239, 1), (205949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (239, 1), (205949, 1)] : List FactorBlock).map factorBlockValue).prod) = 11124129287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_113
      · exact prime_oneHundredTwentyTwoDP_239
      · exact prime_oneHundredTwentyTwoDP_205949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11124129287) ^ 5562064643 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11124129287) ^ 98443622 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11124129287) ^ 46544474 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 11124129287) ^ 54014 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_15584049443 : Nat.Prime 15584049443 := by
  apply lucas_primality 15584049443 (5 : ZMod 15584049443)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (599386517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (599386517, 1)] : List FactorBlock).map factorBlockValue).prod) = 15584049443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_599386517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15584049443) ^ 7792024721 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 15584049443) ^ 1198773034 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 15584049443) ^ 26 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_16598238599 : Nat.Prime 16598238599 := by
  apply lucas_primality 16598238599 (13 : ZMod 16598238599)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8299119299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8299119299, 1)] : List FactorBlock).map factorBlockValue).prod) = 16598238599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_8299119299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 16598238599) ^ 8299119299 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 16598238599) ^ 2 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_20375000519 : Nat.Prime 20375000519 := by
  apply lucas_primality 20375000519 (11 : ZMod 20375000519)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2531, 1), (4025089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2531, 1), (4025089, 1)] : List FactorBlock).map factorBlockValue).prod) = 20375000519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_2531
      · exact prime_oneHundredTwentyTwoDP_4025089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 20375000519) ^ 10187500259 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 20375000519) ^ 8050178 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 20375000519) ^ 5062 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_21873561509 : Nat.Prime 21873561509 := by
  apply lucas_primality 21873561509 (2 : ZMod 21873561509)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5468390377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5468390377, 1)] : List FactorBlock).map factorBlockValue).prod) = 21873561509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5468390377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 21873561509) ^ 10936780754 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21873561509) ^ 4 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_30339944179 : Nat.Prime 30339944179 := by
  apply lucas_primality 30339944179 (2 : ZMod 30339944179)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (2819, 1), (30403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (2819, 1), (30403, 1)] : List FactorBlock).map factorBlockValue).prod) = 30339944179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_59
      · exact prime_oneHundredTwentyTwoDP_2819
      · exact prime_oneHundredTwentyTwoDP_30403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30339944179) ^ 15169972089 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30339944179) ^ 10113314726 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30339944179) ^ 514236342 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30339944179) ^ 10762662 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30339944179) ^ 997926 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_31049061389 : Nat.Prime 31049061389 := by
  apply lucas_primality 31049061389 (2 : ZMod 31049061389)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1091, 1), (7114817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1091, 1), (7114817, 1)] : List FactorBlock).map factorBlockValue).prod) = 31049061389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_1091
      · exact prime_oneHundredTwentyTwoDP_7114817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31049061389) ^ 15524530694 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 31049061389) ^ 28459268 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 31049061389) ^ 4364 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_31188684391 : Nat.Prime 31188684391 := by
  apply lucas_primality 31188684391 (3 : ZMod 31188684391)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1039622813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1039622813, 1)] : List FactorBlock).map factorBlockValue).prod) = 31188684391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_1039622813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31188684391) ^ 15594342195 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31188684391) ^ 10396228130 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31188684391) ^ 6237736878 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31188684391) ^ 30 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_34281646961 : Nat.Prime 34281646961 := by
  apply lucas_primality 34281646961 (3 : ZMod 34281646961)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (38956417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (38956417, 1)] : List FactorBlock).map factorBlockValue).prod) = 34281646961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_38956417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34281646961) ^ 17140823480 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 34281646961) ^ 6856329392 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 34281646961) ^ 3116513360 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 34281646961) ^ 880 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_36270086147 : Nat.Prime 36270086147 := by
  apply lucas_primality 36270086147 (2 : ZMod 36270086147)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (151, 1), (269, 1), (63781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (151, 1), (269, 1), (63781, 1)] : List FactorBlock).map factorBlockValue).prod) = 36270086147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_151
      · exact prime_oneHundredTwentyTwoDP_269
      · exact prime_oneHundredTwentyTwoDP_63781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36270086147) ^ 18135043073 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 36270086147) ^ 5181440878 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 36270086147) ^ 240199246 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 36270086147) ^ 134833034 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 36270086147) ^ 568666 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_36685401289 : Nat.Prime 36685401289 := by
  apply lucas_primality 36685401289 (7 : ZMod 36685401289)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8537, 1), (179051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8537, 1), (179051, 1)] : List FactorBlock).map factorBlockValue).prod) = 36685401289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_8537
      · exact prime_oneHundredTwentyTwoDP_179051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36685401289) ^ 18342700644 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 36685401289) ^ 12228467096 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 36685401289) ^ 4297224 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 36685401289) ^ 204888 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_37731761911 : Nat.Prime 37731761911 := by
  apply lucas_primality 37731761911 (3 : ZMod 37731761911)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (173, 1), (78173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (173, 1), (78173, 1)] : List FactorBlock).map factorBlockValue).prod) = 37731761911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_173
      · exact prime_oneHundredTwentyTwoDP_78173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37731761911) ^ 18865880955 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 37731761911) ^ 12577253970 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 37731761911) ^ 7546352382 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 37731761911) ^ 1217153610 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 37731761911) ^ 218102670 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 37731761911) ^ 482670 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_41278822829 : Nat.Prime 41278822829 := by
  apply lucas_primality 41278822829 (2 : ZMod 41278822829)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2551, 1), (4045357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2551, 1), (4045357, 1)] : List FactorBlock).map factorBlockValue).prod) = 41278822829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_2551
      · exact prime_oneHundredTwentyTwoDP_4045357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41278822829) ^ 20639411414 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 41278822829) ^ 16181428 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 41278822829) ^ 10204 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_47845160171 : Nat.Prime 47845160171 := by
  apply lucas_primality 47845160171 (2 : ZMod 47845160171)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (163, 1), (277, 1), (105967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (163, 1), (277, 1), (105967, 1)] : List FactorBlock).map factorBlockValue).prod) = 47845160171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_163
      · exact prime_oneHundredTwentyTwoDP_277
      · exact prime_oneHundredTwentyTwoDP_105967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47845160171) ^ 23922580085 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 47845160171) ^ 9569032034 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 47845160171) ^ 293528590 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 47845160171) ^ 172726210 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 47845160171) ^ 451510 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_51196563037 : Nat.Prime 51196563037 := by
  apply lucas_primality 51196563037 (17 : ZMod 51196563037)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1422126751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1422126751, 1)] : List FactorBlock).map factorBlockValue).prod) = 51196563037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_1422126751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 51196563037) ^ 25598281518 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 51196563037) ^ 17065521012 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 51196563037) ^ 36 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_59037325643 : Nat.Prime 59037325643 := by
  apply lucas_primality 59037325643 (2 : ZMod 59037325643)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (500316319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (500316319, 1)] : List FactorBlock).map factorBlockValue).prod) = 59037325643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_59
      · exact prime_oneHundredTwentyTwoDP_500316319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59037325643) ^ 29518662821 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 59037325643) ^ 1000632638 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 59037325643) ^ 118 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_67233960817 : Nat.Prime 67233960817 := by
  apply lucas_primality 67233960817 (10 : ZMod 67233960817)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (6311, 1), (20177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (6311, 1), (20177, 1)] : List FactorBlock).map factorBlockValue).prod) = 67233960817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_6311
      · exact prime_oneHundredTwentyTwoDP_20177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 67233960817) ^ 33616980408 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 67233960817) ^ 22411320272 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 67233960817) ^ 6112178256 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 67233960817) ^ 10653456 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 67233960817) ^ 3332208 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_74564700167 : Nat.Prime 74564700167 := by
  apply lucas_primality 74564700167 (11 : ZMod 74564700167)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3389304553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3389304553, 1)] : List FactorBlock).map factorBlockValue).prod) = 74564700167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_3389304553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 74564700167) ^ 37282350083 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 74564700167) ^ 6778609106 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 74564700167) ^ 22 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_75675267191 : Nat.Prime 75675267191 := by
  apply lucas_primality 75675267191 (17 : ZMod 75675267191)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (113, 1), (193, 1), (6547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (113, 1), (193, 1), (6547, 1)] : List FactorBlock).map factorBlockValue).prod) = 75675267191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_53
      · exact prime_oneHundredTwentyTwoDP_113
      · exact prime_oneHundredTwentyTwoDP_193
      · exact prime_oneHundredTwentyTwoDP_6547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 75675267191) ^ 37837633595 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 75675267191) ^ 15135053438 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 75675267191) ^ 1427835230 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 75675267191) ^ 669692630 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 75675267191) ^ 392099830 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (17 : ZMod 75675267191) ^ 11558770 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_83373841303 : Nat.Prime 83373841303 := by
  apply lucas_primality 83373841303 (3 : ZMod 83373841303)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (817390601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (817390601, 1)] : List FactorBlock).map factorBlockValue).prod) = 83373841303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_817390601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 83373841303) ^ 41686920651 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 83373841303) ^ 27791280434 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 83373841303) ^ 4904343606 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 83373841303) ^ 102 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_93067450097 : Nat.Prime 93067450097 := by
  apply lucas_primality 93067450097 (3 : ZMod 93067450097)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (3623, 1), (94441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (3623, 1), (94441, 1)] : List FactorBlock).map factorBlockValue).prod) = 93067450097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_3623
      · exact prime_oneHundredTwentyTwoDP_94441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 93067450097) ^ 46533725048 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 93067450097) ^ 5474555888 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 93067450097) ^ 25687952 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 93067450097) ^ 985456 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_94263648329 : Nat.Prime 94263648329 := by
  apply lucas_primality 94263648329 (3 : ZMod 94263648329)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (167, 1), (2432987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (167, 1), (2432987, 1)] : List FactorBlock).map factorBlockValue).prod) = 94263648329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_29
      · exact prime_oneHundredTwentyTwoDP_167
      · exact prime_oneHundredTwentyTwoDP_2432987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 94263648329) ^ 47131824164 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 94263648329) ^ 3250470632 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 94263648329) ^ 564452984 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 94263648329) ^ 38744 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_100633456177 : Nat.Prime 100633456177 := by
  apply lucas_primality 100633456177 (5 : ZMod 100633456177)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 2), (17326697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 2), (17326697, 1)] : List FactorBlock).map factorBlockValue).prod) = 100633456177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_17326697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 100633456177) ^ 50316728088 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 100633456177) ^ 33544485392 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 100633456177) ^ 9148496016 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 100633456177) ^ 5808 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_109114985501 : Nat.Prime 109114985501 := by
  apply lucas_primality 109114985501 (2 : ZMod 109114985501)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (12547, 1), (17393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (12547, 1), (17393, 1)] : List FactorBlock).map factorBlockValue).prod) = 109114985501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_12547
      · exact prime_oneHundredTwentyTwoDP_17393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 109114985501) ^ 54557492750 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 109114985501) ^ 21822997100 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 109114985501) ^ 8696500 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 109114985501) ^ 6273500 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_136503012103 : Nat.Prime 136503012103 := by
  apply lucas_primality 136503012103 (5 : ZMod 136503012103)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (149, 1), (167, 1), (48121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (149, 1), (167, 1), (48121, 1)] : List FactorBlock).map factorBlockValue).prod) = 136503012103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_149
      · exact prime_oneHundredTwentyTwoDP_167
      · exact prime_oneHundredTwentyTwoDP_48121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 136503012103) ^ 68251506051 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136503012103) ^ 45501004034 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136503012103) ^ 7184369058 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136503012103) ^ 916127598 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136503012103) ^ 817383306 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 136503012103) ^ 2836662 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_142247822149 : Nat.Prime 142247822149 := by
  apply lucas_primality 142247822149 (2 : ZMod 142247822149)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3951328393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3951328393, 1)] : List FactorBlock).map factorBlockValue).prod) = 142247822149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_3951328393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 142247822149) ^ 71123911074 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 142247822149) ^ 47415940716 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 142247822149) ^ 36 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_148579600339 : Nat.Prime 148579600339 := by
  apply lucas_primality 148579600339 (3 : ZMod 148579600339)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (37, 1), (17160961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (37, 1), (17160961, 1)] : List FactorBlock).map factorBlockValue).prod) = 148579600339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_37
      · exact prime_oneHundredTwentyTwoDP_17160961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 148579600339) ^ 74289800169 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 148579600339) ^ 49526533446 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 148579600339) ^ 11429200026 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 148579600339) ^ 4015664874 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 148579600339) ^ 8658 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_159654481919 : Nat.Prime 159654481919 := by
  apply lucas_primality 159654481919 (7 : ZMod 159654481919)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (97, 1), (1471, 1), (18047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (97, 1), (1471, 1), (18047, 1)] : List FactorBlock).map factorBlockValue).prod) = 159654481919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_97
      · exact prime_oneHundredTwentyTwoDP_1471
      · exact prime_oneHundredTwentyTwoDP_18047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 159654481919) ^ 79827240959 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 159654481919) ^ 5150144578 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 159654481919) ^ 1645922494 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 159654481919) ^ 108534658 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 159654481919) ^ 8846594 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_159695036621 : Nat.Prime 159695036621 := by
  apply lucas_primality 159695036621 (2 : ZMod 159695036621)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (61, 1), (181, 1), (14759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (61, 1), (181, 1), (14759, 1)] : List FactorBlock).map factorBlockValue).prod) = 159695036621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_61
      · exact prime_oneHundredTwentyTwoDP_181
      · exact prime_oneHundredTwentyTwoDP_14759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 159695036621) ^ 79847518310 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 159695036621) ^ 31939007324 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 159695036621) ^ 22813576660 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 159695036621) ^ 2617951420 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 159695036621) ^ 882293020 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 159695036621) ^ 10820180 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_162218890357 : Nat.Prime 162218890357 := by
  apply lucas_primality 162218890357 (5 : ZMod 162218890357)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (67, 1), (257, 1), (46181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (67, 1), (257, 1), (46181, 1)] : List FactorBlock).map factorBlockValue).prod) = 162218890357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_67
      · exact prime_oneHundredTwentyTwoDP_257
      · exact prime_oneHundredTwentyTwoDP_46181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 162218890357) ^ 81109445178 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 162218890357) ^ 54072963452 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 162218890357) ^ 9542287668 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 162218890357) ^ 2421177468 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 162218890357) ^ 631201908 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 162218890357) ^ 3512676 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_192987195757 : Nat.Prime 192987195757 := by
  apply lucas_primality 192987195757 (2 : ZMod 192987195757)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (342175879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (342175879, 1)] : List FactorBlock).map factorBlockValue).prod) = 192987195757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_47
      · exact prime_oneHundredTwentyTwoDP_342175879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 192987195757) ^ 96493597878 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 192987195757) ^ 64329065252 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 192987195757) ^ 4106110548 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 192987195757) ^ 564 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_210867554899 : Nat.Prime 210867554899 := by
  apply lucas_primality 210867554899 (10 : ZMod 210867554899)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (13, 1), (11703161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (13, 1), (11703161, 1)] : List FactorBlock).map factorBlockValue).prod) = 210867554899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_11703161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 210867554899) ^ 105433777449 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 210867554899) ^ 70289184966 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 210867554899) ^ 30123936414 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 210867554899) ^ 19169777718 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 210867554899) ^ 16220581146 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 210867554899) ^ 18018 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_212201760467 : Nat.Prime 212201760467 := by
  apply lucas_primality 212201760467 (2 : ZMod 212201760467)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (43, 1), (9829, 1), (14767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (43, 1), (9829, 1), (14767, 1)] : List FactorBlock).map factorBlockValue).prod) = 212201760467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_43
      · exact prime_oneHundredTwentyTwoDP_9829
      · exact prime_oneHundredTwentyTwoDP_14767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 212201760467) ^ 106100880233 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 212201760467) ^ 12482456498 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 212201760467) ^ 4934924662 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 212201760467) ^ 21589354 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 212201760467) ^ 14369998 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_230862363931 : Nat.Prime 230862363931 := by
  apply lucas_primality 230862363931 (2 : ZMod 230862363931)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (29, 1), (31, 1), (47, 1), (5519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (29, 1), (31, 1), (47, 1), (5519, 1)] : List FactorBlock).map factorBlockValue).prod) = 230862363931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_29
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_47
      · exact prime_oneHundredTwentyTwoDP_5519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 230862363931) ^ 115431181965 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230862363931) ^ 76954121310 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230862363931) ^ 46172472786 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230862363931) ^ 20987487630 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230862363931) ^ 7960771170 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230862363931) ^ 7447173030 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230862363931) ^ 4911965190 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230862363931) ^ 41830470 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_268935843269 : Nat.Prime 268935843269 := by
  apply lucas_primality 268935843269 (2 : ZMod 268935843269)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67233960817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67233960817, 1)] : List FactorBlock).map factorBlockValue).prod) = 268935843269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_67233960817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 268935843269) ^ 134467921634 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 268935843269) ^ 4 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_408062215003 : Nat.Prime 408062215003 := by
  apply lucas_primality 408062215003 (5 : ZMod 408062215003)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (307739227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (307739227, 1)] : List FactorBlock).map factorBlockValue).prod) = 408062215003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_307739227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 408062215003) ^ 204031107501 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 408062215003) ^ 136020738334 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 408062215003) ^ 31389401154 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 408062215003) ^ 24003659706 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 408062215003) ^ 1326 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_427664667707 : Nat.Prime 427664667707 := by
  apply lucas_primality 427664667707 (2 : ZMod 427664667707)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (509, 1), (1203733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (509, 1), (1203733, 1)] : List FactorBlock).map factorBlockValue).prod) = 427664667707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_349
      · exact prime_oneHundredTwentyTwoDP_509
      · exact prime_oneHundredTwentyTwoDP_1203733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 427664667707) ^ 213832333853 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 427664667707) ^ 1225400194 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 427664667707) ^ 840205634 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 427664667707) ^ 355282 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_454558977709 : Nat.Prime 454558977709 := by
  apply lucas_primality 454558977709 (2 : ZMod 454558977709)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (3443628619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (3443628619, 1)] : List FactorBlock).map factorBlockValue).prod) = 454558977709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_3443628619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 454558977709) ^ 227279488854 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 454558977709) ^ 151519659236 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 454558977709) ^ 41323543428 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 454558977709) ^ 132 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_500243047819 : Nat.Prime 500243047819 := by
  apply lucas_primality 500243047819 (2 : ZMod 500243047819)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83373841303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83373841303, 1)] : List FactorBlock).map factorBlockValue).prod) = 500243047819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_83373841303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 500243047819) ^ 250121523909 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 500243047819) ^ 166747682606 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 500243047819) ^ 6 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_548481622849 : Nat.Prime 548481622849 := by
  apply lucas_primality 548481622849 (7 : ZMod 548481622849)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (2856675119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (2856675119, 1)] : List FactorBlock).map factorBlockValue).prod) = 548481622849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_2856675119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 548481622849) ^ 274240811424 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 548481622849) ^ 182827207616 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 548481622849) ^ 192 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_560582208343 : Nat.Prime 560582208343 := by
  apply lucas_primality 560582208343 (3 : ZMod 560582208343)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1583, 1), (1513361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1583, 1), (1513361, 1)] : List FactorBlock).map factorBlockValue).prod) = 560582208343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_1583
      · exact prime_oneHundredTwentyTwoDP_1513361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 560582208343) ^ 280291104171 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 560582208343) ^ 186860736114 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 560582208343) ^ 43121708334 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 560582208343) ^ 354126474 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 560582208343) ^ 370422 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_587081730419 : Nat.Prime 587081730419 := by
  apply lucas_primality 587081730419 (2 : ZMod 587081730419)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8387, 1), (34999507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8387, 1), (34999507, 1)] : List FactorBlock).map factorBlockValue).prod) = 587081730419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_8387
      · exact prime_oneHundredTwentyTwoDP_34999507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 587081730419) ^ 293540865209 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 587081730419) ^ 69999014 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 587081730419) ^ 16774 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_647918105509 : Nat.Prime 647918105509 := by
  apply lucas_primality 647918105509 (2 : ZMod 647918105509)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (431, 1), (41758063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (431, 1), (41758063, 1)] : List FactorBlock).map factorBlockValue).prod) = 647918105509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_431
      · exact prime_oneHundredTwentyTwoDP_41758063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 647918105509) ^ 323959052754 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 647918105509) ^ 215972701836 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 647918105509) ^ 1503290268 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 647918105509) ^ 15516 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_648875561429 : Nat.Prime 648875561429 := by
  apply lucas_primality 648875561429 (2 : ZMod 648875561429)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (162218890357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (162218890357, 1)] : List FactorBlock).map factorBlockValue).prod) = 648875561429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_162218890357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 648875561429) ^ 324437780714 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 648875561429) ^ 4 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_734741716477 : Nat.Prime 734741716477 := by
  apply lucas_primality 734741716477 (2 : ZMod 734741716477)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1013, 1), (60442721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1013, 1), (60442721, 1)] : List FactorBlock).map factorBlockValue).prod) = 734741716477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_1013
      · exact prime_oneHundredTwentyTwoDP_60442721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 734741716477) ^ 367370858238 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 734741716477) ^ 244913905492 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 734741716477) ^ 725312652 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 734741716477) ^ 12156 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_773888373239 : Nat.Prime 773888373239 := by
  apply lucas_primality 773888373239 (7 : ZMod 773888373239)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1499, 1), (258134881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1499, 1), (258134881, 1)] : List FactorBlock).map factorBlockValue).prod) = 773888373239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_1499
      · exact prime_oneHundredTwentyTwoDP_258134881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 773888373239) ^ 386944186619 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 773888373239) ^ 516269762 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 773888373239) ^ 2998 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_815541347261 : Nat.Prime 815541347261 := by
  apply lucas_primality 815541347261 (2 : ZMod 815541347261)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1259, 1), (32388457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1259, 1), (32388457, 1)] : List FactorBlock).map factorBlockValue).prod) = 815541347261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_1259
      · exact prime_oneHundredTwentyTwoDP_32388457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 815541347261) ^ 407770673630 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 815541347261) ^ 163108269452 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 815541347261) ^ 647769140 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 815541347261) ^ 25180 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_859136992927 : Nat.Prime 859136992927 := by
  apply lucas_primality 859136992927 (3 : ZMod 859136992927)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (53, 1), (8431, 1), (10337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (53, 1), (8431, 1), (10337, 1)] : List FactorBlock).map factorBlockValue).prod) = 859136992927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_53
      · exact prime_oneHundredTwentyTwoDP_8431
      · exact prime_oneHundredTwentyTwoDP_10337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 859136992927) ^ 429568496463 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 859136992927) ^ 286378997642 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 859136992927) ^ 27714096546 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 859136992927) ^ 16210131942 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 859136992927) ^ 101902146 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 859136992927) ^ 83112798 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_961176771587 : Nat.Prime 961176771587 := by
  apply lucas_primality 961176771587 (2 : ZMod 961176771587)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (281, 1), (1879, 1), (910207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (281, 1), (1879, 1), (910207, 1)] : List FactorBlock).map factorBlockValue).prod) = 961176771587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_281
      · exact prime_oneHundredTwentyTwoDP_1879
      · exact prime_oneHundredTwentyTwoDP_910207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 961176771587) ^ 480588385793 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 961176771587) ^ 3420557906 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 961176771587) ^ 511536334 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 961176771587) ^ 1055998 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_970352199613 : Nat.Prime 970352199613 := by
  apply lucas_primality 970352199613 (2 : ZMod 970352199613)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (8984742589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (8984742589, 1)] : List FactorBlock).map factorBlockValue).prod) = 970352199613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_8984742589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 970352199613) ^ 485176099806 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 970352199613) ^ 323450733204 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 970352199613) ^ 108 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1046839207637 : Nat.Prime 1046839207637 := by
  apply lucas_primality 1046839207637 (2 : ZMod 1046839207637)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (809, 1), (1031, 1), (7297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (809, 1), (1031, 1), (7297, 1)] : List FactorBlock).map factorBlockValue).prod) = 1046839207637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_43
      · exact prime_oneHundredTwentyTwoDP_809
      · exact prime_oneHundredTwentyTwoDP_1031
      · exact prime_oneHundredTwentyTwoDP_7297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1046839207637) ^ 523419603818 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1046839207637) ^ 24345097852 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1046839207637) ^ 1293991604 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1046839207637) ^ 1015362956 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1046839207637) ^ 143461588 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1247303643827 : Nat.Prime 1247303643827 := by
  apply lucas_primality 1247303643827 (2 : ZMod 1247303643827)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (36685401289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (36685401289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1247303643827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_36685401289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1247303643827) ^ 623651821913 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247303643827) ^ 73370802578 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247303643827) ^ 34 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1385174183587 : Nat.Prime 1385174183587 := by
  apply lucas_primality 1385174183587 (5 : ZMod 1385174183587)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (230862363931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (230862363931, 1)] : List FactorBlock).map factorBlockValue).prod) = 1385174183587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_230862363931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1385174183587) ^ 692587091793 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1385174183587) ^ 461724727862 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1385174183587) ^ 6 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1455900328741 : Nat.Prime 1455900328741 := by
  apply lucas_primality 1455900328741 (6 : ZMod 1455900328741)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (43, 1), (89, 1), (101, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 1), (43, 1), (89, 1), (101, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1455900328741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_43
      · exact prime_oneHundredTwentyTwoDP_89
      · exact prime_oneHundredTwentyTwoDP_101
      · exact prime_oneHundredTwentyTwoDP_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1455900328741) ^ 727950164370 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1455900328741) ^ 485300109580 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1455900328741) ^ 291180065748 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1455900328741) ^ 132354575340 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1455900328741) ^ 111992332980 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1455900328741) ^ 33858147180 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1455900328741) ^ 16358430660 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1455900328741) ^ 14414854740 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1455900328741) ^ 3316401660 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1587105308263 : Nat.Prime 1587105308263 := by
  apply lucas_primality 1587105308263 (3 : ZMod 1587105308263)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1867, 1), (141680531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1867, 1), (141680531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1587105308263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_1867
      · exact prime_oneHundredTwentyTwoDP_141680531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1587105308263) ^ 793552654131 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1587105308263) ^ 529035102754 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1587105308263) ^ 850083186 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1587105308263) ^ 11202 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1869969156859 : Nat.Prime 1869969156859 := by
  apply lucas_primality 1869969156859 (3 : ZMod 1869969156859)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (9444288671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (9444288671, 1)] : List FactorBlock).map factorBlockValue).prod) = 1869969156859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_9444288671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1869969156859) ^ 934984578429 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1869969156859) ^ 623323052286 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1869969156859) ^ 169997196078 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1869969156859) ^ 198 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3509671871473 : Nat.Prime 3509671871473 := by
  apply lucas_primality 3509671871473 (5 : ZMod 3509671871473)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (107, 1), (52565179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (107, 1), (52565179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3509671871473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_107
      · exact prime_oneHundredTwentyTwoDP_52565179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3509671871473) ^ 1754835935736 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3509671871473) ^ 1169890623824 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3509671871473) ^ 269974759344 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3509671871473) ^ 32800671696 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3509671871473) ^ 66768 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3951310427063 : Nat.Prime 3951310427063 := by
  apply lucas_primality 3951310427063 (5 : ZMod 3951310427063)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (410243, 1), (4815817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (410243, 1), (4815817, 1)] : List FactorBlock).map factorBlockValue).prod) = 3951310427063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_410243
      · exact prime_oneHundredTwentyTwoDP_4815817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3951310427063) ^ 1975655213531 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951310427063) ^ 9631634 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3951310427063) ^ 820486 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3983256919091 : Nat.Prime 3983256919091 := by
  apply lucas_primality 3983256919091 (6 : ZMod 3983256919091)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (138371, 1), (2878679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (138371, 1), (2878679, 1)] : List FactorBlock).map factorBlockValue).prod) = 3983256919091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_138371
      · exact prime_oneHundredTwentyTwoDP_2878679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3983256919091) ^ 1991628459545 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 3983256919091) ^ 796651383818 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 3983256919091) ^ 28786790 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 3983256919091) ^ 1383710 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_4541967206407 : Nat.Prime 4541967206407 := by
  apply lucas_primality 4541967206407 (7 : ZMod 4541967206407)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (5149622683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (5149622683, 1)] : List FactorBlock).map factorBlockValue).prod) = 4541967206407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_5149622683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4541967206407) ^ 2270983603203 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4541967206407) ^ 1513989068802 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4541967206407) ^ 648852458058 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 4541967206407) ^ 882 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_4997064247327 : Nat.Prime 4997064247327 := by
  apply lucas_primality 4997064247327 (3 : ZMod 4997064247327)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (162823, 1), (1705009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (162823, 1), (1705009, 1)] : List FactorBlock).map factorBlockValue).prod) = 4997064247327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_162823
      · exact prime_oneHundredTwentyTwoDP_1705009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4997064247327) ^ 2498532123663 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4997064247327) ^ 1665688082442 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4997064247327) ^ 30690162 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4997064247327) ^ 2930814 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_5154821957563 : Nat.Prime 5154821957563 := by
  apply lucas_primality 5154821957563 (2 : ZMod 5154821957563)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (859136992927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (859136992927, 1)] : List FactorBlock).map factorBlockValue).prod) = 5154821957563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_859136992927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5154821957563) ^ 2577410978781 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5154821957563) ^ 1718273985854 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5154821957563) ^ 6 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_5185826420869 : Nat.Prime 5185826420869 := by
  apply lucas_primality 5185826420869 (10 : ZMod 5185826420869)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (83, 1), (131, 1), (337, 1), (39313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (83, 1), (131, 1), (337, 1), (39313, 1)] : List FactorBlock).map factorBlockValue).prod) = 5185826420869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_83
      · exact prime_oneHundredTwentyTwoDP_131
      · exact prime_oneHundredTwentyTwoDP_337
      · exact prime_oneHundredTwentyTwoDP_39313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5185826420869) ^ 2592913210434 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 5185826420869) ^ 1728608806956 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 5185826420869) ^ 62479836396 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 5185826420869) ^ 39586461228 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 5185826420869) ^ 15388208964 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 5185826420869) ^ 131911236 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_6348421233053 : Nat.Prime 6348421233053 := by
  apply lucas_primality 6348421233053 (2 : ZMod 6348421233053)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1587105308263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1587105308263, 1)] : List FactorBlock).map factorBlockValue).prod) = 6348421233053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_1587105308263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6348421233053) ^ 3174210616526 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6348421233053) ^ 4 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_6432629569997 : Nat.Prime 6432629569997 := by
  apply lucas_primality 6432629569997 (2 : ZMod 6432629569997)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (163, 1), (1409428039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (163, 1), (1409428039, 1)] : List FactorBlock).map factorBlockValue).prod) = 6432629569997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_163
      · exact prime_oneHundredTwentyTwoDP_1409428039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6432629569997) ^ 3216314784998 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6432629569997) ^ 918947081428 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6432629569997) ^ 39463985092 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6432629569997) ^ 4564 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_7479876627437 : Nat.Prime 7479876627437 := by
  apply lucas_primality 7479876627437 (2 : ZMod 7479876627437)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1869969156859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1869969156859, 1)] : List FactorBlock).map factorBlockValue).prod) = 7479876627437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_1869969156859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7479876627437) ^ 3739938313718 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7479876627437) ^ 4 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_7786534188401 : Nat.Prime 7786534188401 := by
  apply lucas_primality 7786534188401 (3 : ZMod 7786534188401)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (11, 1), (10369, 1), (170669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (11, 1), (10369, 1), (170669, 1)] : List FactorBlock).map factorBlockValue).prod) = 7786534188401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_10369
      · exact prime_oneHundredTwentyTwoDP_170669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7786534188401) ^ 3893267094200 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 7786534188401) ^ 1557306837680 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 7786534188401) ^ 707866744400 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 7786534188401) ^ 750943600 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 7786534188401) ^ 45623600 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_11876028528479 : Nat.Prime 11876028528479 := by
  apply lucas_primality 11876028528479 (11 : ZMod 11876028528479)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (197, 1), (1187, 1), (305947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (197, 1), (1187, 1), (305947, 1)] : List FactorBlock).map factorBlockValue).prod) = 11876028528479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_83
      · exact prime_oneHundredTwentyTwoDP_197
      · exact prime_oneHundredTwentyTwoDP_1187
      · exact prime_oneHundredTwentyTwoDP_305947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11876028528479) ^ 5938014264239 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 11876028528479) ^ 143084681066 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 11876028528479) ^ 60284408774 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 11876028528479) ^ 10005078794 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 11876028528479) ^ 38817274 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_12105247839929 : Nat.Prime 12105247839929 := by
  apply lucas_primality 12105247839929 (3 : ZMod 12105247839929)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (239, 1), (5441, 1), (1163609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (239, 1), (5441, 1), (1163609, 1)] : List FactorBlock).map factorBlockValue).prod) = 12105247839929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_239
      · exact prime_oneHundredTwentyTwoDP_5441
      · exact prime_oneHundredTwentyTwoDP_1163609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12105247839929) ^ 6052623919964 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12105247839929) ^ 50649572552 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12105247839929) ^ 2224820408 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12105247839929) ^ 10403192 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_13761397726253 : Nat.Prime 13761397726253 := by
  apply lucas_primality 13761397726253 (2 : ZMod 13761397726253)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (181, 1), (571, 1), (3026183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (181, 1), (571, 1), (3026183, 1)] : List FactorBlock).map factorBlockValue).prod) = 13761397726253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_181
      · exact prime_oneHundredTwentyTwoDP_571
      · exact prime_oneHundredTwentyTwoDP_3026183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13761397726253) ^ 6880698863126 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13761397726253) ^ 1251036156932 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13761397726253) ^ 76029821692 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13761397726253) ^ 24100521412 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13761397726253) ^ 4547444 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_14476107892693 : Nat.Prime 14476107892693 := by
  apply lucas_primality 14476107892693 (2 : ZMod 14476107892693)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (170239, 1), (7086169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (170239, 1), (7086169, 1)] : List FactorBlock).map factorBlockValue).prod) = 14476107892693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_170239
      · exact prime_oneHundredTwentyTwoDP_7086169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14476107892693) ^ 7238053946346 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14476107892693) ^ 4825369297564 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14476107892693) ^ 85034028 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14476107892693) ^ 2042868 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_16612882433321 : Nat.Prime 16612882433321 := by
  apply lucas_primality 16612882433321 (6 : ZMod 16612882433321)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (83, 1), (7823, 1), (639637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (83, 1), (7823, 1), (639637, 1)] : List FactorBlock).map factorBlockValue).prod) = 16612882433321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_83
      · exact prime_oneHundredTwentyTwoDP_7823
      · exact prime_oneHundredTwentyTwoDP_639637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16612882433321) ^ 8306441216660 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16612882433321) ^ 3322576486664 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16612882433321) ^ 200155210040 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16612882433321) ^ 2123594840 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16612882433321) ^ 25972360 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_21224320418507 : Nat.Prime 21224320418507 := by
  apply lucas_primality 21224320418507 (2 : ZMod 21224320418507)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 2), (73, 1), (157, 1), (500777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 2), (73, 1), (157, 1), (500777, 1)] : List FactorBlock).map factorBlockValue).prod) = 21224320418507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_43
      · exact prime_oneHundredTwentyTwoDP_73
      · exact prime_oneHundredTwentyTwoDP_157
      · exact prime_oneHundredTwentyTwoDP_500777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21224320418507) ^ 10612160209253 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21224320418507) ^ 493588846942 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21224320418507) ^ 290744115322 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21224320418507) ^ 135186754258 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 21224320418507) ^ 42382778 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_26332798765073 : Nat.Prime 26332798765073 := by
  apply lucas_primality 26332798765073 (3 : ZMod 26332798765073)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (14083, 1), (116864299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (14083, 1), (116864299, 1)] : List FactorBlock).map factorBlockValue).prod) = 26332798765073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_14083
      · exact prime_oneHundredTwentyTwoDP_116864299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26332798765073) ^ 13166399382536 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26332798765073) ^ 1869828784 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 26332798765073) ^ 225328 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_28846993512509 : Nat.Prime 28846993512509 := by
  apply lucas_primality 28846993512509 (2 : ZMod 28846993512509)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (5653, 1), (75043427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (5653, 1), (75043427, 1)] : List FactorBlock).map factorBlockValue).prod) = 28846993512509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_5653
      · exact prime_oneHundredTwentyTwoDP_75043427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28846993512509) ^ 14423496756254 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28846993512509) ^ 1696881971324 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28846993512509) ^ 5102953036 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28846993512509) ^ 384404 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_32282362535117 : Nat.Prime 32282362535117 := by
  apply lucas_primality 32282362535117 (2 : ZMod 32282362535117)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (2659, 1), (104661989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (2659, 1), (104661989, 1)] : List FactorBlock).map factorBlockValue).prod) = 32282362535117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_29
      · exact prime_oneHundredTwentyTwoDP_2659
      · exact prime_oneHundredTwentyTwoDP_104661989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32282362535117) ^ 16141181267558 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 32282362535117) ^ 1113184915004 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 32282362535117) ^ 12140790724 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 32282362535117) ^ 308444 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_32441156753849 : Nat.Prime 32441156753849 := by
  apply lucas_primality 32441156753849 (3 : ZMod 32441156753849)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (409, 1), (168047101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (409, 1), (168047101, 1)] : List FactorBlock).map factorBlockValue).prod) = 32441156753849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_59
      · exact prime_oneHundredTwentyTwoDP_409
      · exact prime_oneHundredTwentyTwoDP_168047101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32441156753849) ^ 16220578376924 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32441156753849) ^ 549850114472 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32441156753849) ^ 79318231672 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32441156753849) ^ 193048 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_34461248638483 : Nat.Prime 34461248638483 := by
  apply lucas_primality 34461248638483 (5 : ZMod 34461248638483)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (4297, 1), (6967, 1), (21317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (4297, 1), (6967, 1), (21317, 1)] : List FactorBlock).map factorBlockValue).prod) = 34461248638483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_4297
      · exact prime_oneHundredTwentyTwoDP_6967
      · exact prime_oneHundredTwentyTwoDP_21317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34461248638483) ^ 17230624319241 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34461248638483) ^ 11487082879494 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34461248638483) ^ 8019839106 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34461248638483) ^ 4946354046 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 34461248638483) ^ 1616608746 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_50541385649353 : Nat.Prime 50541385649353 := by
  apply lucas_primality 50541385649353 (5 : ZMod 50541385649353)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (17, 2), (560524639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (17, 2), (560524639, 1)] : List FactorBlock).map factorBlockValue).prod) = 50541385649353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_560524639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 50541385649353) ^ 25270692824676 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50541385649353) ^ 16847128549784 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50541385649353) ^ 3887798896104 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50541385649353) ^ 2973022685256 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50541385649353) ^ 90168 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_66623571467749 : Nat.Prime 66623571467749 := by
  apply lucas_primality 66623571467749 (2 : ZMod 66623571467749)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (331, 1), (7457, 1), (749779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (331, 1), (7457, 1), (749779, 1)] : List FactorBlock).map factorBlockValue).prod) = 66623571467749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_331
      · exact prime_oneHundredTwentyTwoDP_7457
      · exact prime_oneHundredTwentyTwoDP_749779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66623571467749) ^ 33311785733874 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 66623571467749) ^ 22207857155916 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 66623571467749) ^ 201279672108 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 66623571467749) ^ 8934366564 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 66623571467749) ^ 88857612 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_81069606011903 : Nat.Prime 81069606011903 := by
  apply lucas_primality 81069606011903 (5 : ZMod 81069606011903)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2503, 1), (121007, 1), (133831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2503, 1), (121007, 1), (133831, 1)] : List FactorBlock).map factorBlockValue).prod) = 81069606011903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_2503
      · exact prime_oneHundredTwentyTwoDP_121007
      · exact prime_oneHundredTwentyTwoDP_133831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 81069606011903) ^ 40534803005951 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 81069606011903) ^ 32388975634 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 81069606011903) ^ 669957986 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 81069606011903) ^ 605761042 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_82924093277041 : Nat.Prime 82924093277041 := by
  apply lucas_primality 82924093277041 (19 : ZMod 82924093277041)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (1901, 1), (181755421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (1901, 1), (181755421, 1)] : List FactorBlock).map factorBlockValue).prod) = 82924093277041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_1901
      · exact prime_oneHundredTwentyTwoDP_181755421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 82924093277041) ^ 41462046638520 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 82924093277041) ^ 27641364425680 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 82924093277041) ^ 16584818655408 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 82924093277041) ^ 43621301040 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 82924093277041) ^ 456240 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_86156974572707 : Nat.Prime 86156974572707 := by
  apply lucas_primality 86156974572707 (2 : ZMod 86156974572707)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (457, 1), (94263648329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (457, 1), (94263648329, 1)] : List FactorBlock).map factorBlockValue).prod) = 86156974572707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_457
      · exact prime_oneHundredTwentyTwoDP_94263648329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86156974572707) ^ 43078487286353 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 86156974572707) ^ 188527296658 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 86156974572707) ^ 914 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_115932783265031 : Nat.Prime 115932783265031 := by
  apply lucas_primality 115932783265031 (13 : ZMod 115932783265031)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2314759, 1), (5008417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2314759, 1), (5008417, 1)] : List FactorBlock).map factorBlockValue).prod) = 115932783265031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_2314759
      · exact prime_oneHundredTwentyTwoDP_5008417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 115932783265031) ^ 57966391632515 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 115932783265031) ^ 23186556653006 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 115932783265031) ^ 50084170 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 115932783265031) ^ 23147590 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_132702447558547 : Nat.Prime 132702447558547 := by
  apply lucas_primality 132702447558547 (2 : ZMod 132702447558547)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (32401, 1), (227534897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (32401, 1), (227534897, 1)] : List FactorBlock).map factorBlockValue).prod) = 132702447558547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_32401
      · exact prime_oneHundredTwentyTwoDP_227534897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 132702447558547) ^ 66351223779273 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 132702447558547) ^ 44234149186182 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 132702447558547) ^ 4095628146 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 132702447558547) ^ 583218 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_132798727962997 : Nat.Prime 132798727962997 := by
  apply lucas_primality 132798727962997 (5 : ZMod 132798727962997)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5059, 1), (2187499637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5059, 1), (2187499637, 1)] : List FactorBlock).map factorBlockValue).prod) = 132798727962997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5059
      · exact prime_oneHundredTwentyTwoDP_2187499637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 132798727962997) ^ 66399363981498 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 132798727962997) ^ 44266242654332 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 132798727962997) ^ 26249995644 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 132798727962997) ^ 60708 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_149080276366271 : Nat.Prime 149080276366271 := by
  apply lucas_primality 149080276366271 (19 : ZMod 149080276366271)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (197, 1), (75675267191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (197, 1), (75675267191, 1)] : List FactorBlock).map factorBlockValue).prod) = 149080276366271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_197
      · exact prime_oneHundredTwentyTwoDP_75675267191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 149080276366271) ^ 74540138183135 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 149080276366271) ^ 29816055273254 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 149080276366271) ^ 756752671910 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 149080276366271) ^ 1970 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_159923515384067 : Nat.Prime 159923515384067 := by
  apply lucas_primality 159923515384067 (5 : ZMod 159923515384067)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (733, 1), (15584049443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (733, 1), (15584049443, 1)] : List FactorBlock).map factorBlockValue).prod) = 159923515384067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_733
      · exact prime_oneHundredTwentyTwoDP_15584049443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 159923515384067) ^ 79961757692033 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 159923515384067) ^ 22846216483438 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 159923515384067) ^ 218176692202 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 159923515384067) ^ 10262 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_178900451188579 : Nat.Prime 178900451188579 := by
  apply lucas_primality 178900451188579 (2 : ZMod 178900451188579)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (193, 1), (1187, 1), (688637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (193, 1), (1187, 1), (688637, 1)] : List FactorBlock).map factorBlockValue).prod) = 178900451188579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_193
      · exact prime_oneHundredTwentyTwoDP_1187
      · exact prime_oneHundredTwentyTwoDP_688637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178900451188579) ^ 89450225594289 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 178900451188579) ^ 59633483729526 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 178900451188579) ^ 25557207312654 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 178900451188579) ^ 926945342946 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 178900451188579) ^ 150716471094 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 178900451188579) ^ 259789194 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_190465374346769 : Nat.Prime 190465374346769 := by
  apply lucas_primality 190465374346769 (3 : ZMod 190465374346769)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 2), (158993, 1), (207401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 2), (158993, 1), (207401, 1)] : List FactorBlock).map factorBlockValue).prod) = 190465374346769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_158993
      · exact prime_oneHundredTwentyTwoDP_207401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 190465374346769) ^ 95232687173384 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 190465374346769) ^ 10024493386672 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 190465374346769) ^ 1197948176 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 190465374346769) ^ 918343568 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_197453384225641 : Nat.Prime 197453384225641 := by
  apply lucas_primality 197453384225641 (13 : ZMod 197453384225641)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (548481622849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (548481622849, 1)] : List FactorBlock).map factorBlockValue).prod) = 197453384225641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_548481622849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 197453384225641) ^ 98726692112820 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 197453384225641) ^ 65817794741880 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 197453384225641) ^ 39490676845128 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 197453384225641) ^ 360 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_215803096946837 : Nat.Prime 215803096946837 := by
  apply lucas_primality 215803096946837 (2 : ZMod 215803096946837)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (47, 1), (1049, 1), (8227591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (47, 1), (1049, 1), (8227591, 1)] : List FactorBlock).map factorBlockValue).prod) = 215803096946837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_47
      · exact prime_oneHundredTwentyTwoDP_1049
      · exact prime_oneHundredTwentyTwoDP_8227591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 215803096946837) ^ 107901548473418 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 215803096946837) ^ 30829013849548 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 215803096946837) ^ 11358057734044 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 215803096946837) ^ 4591555254188 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 215803096946837) ^ 205722685364 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 215803096946837) ^ 26229196 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_249859727374643 : Nat.Prime 249859727374643 := by
  apply lucas_primality 249859727374643 (2 : ZMod 249859727374643)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (43, 1), (37731761911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (43, 1), (37731761911, 1)] : List FactorBlock).map factorBlockValue).prod) = 249859727374643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_43
      · exact prime_oneHundredTwentyTwoDP_37731761911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 249859727374643) ^ 124929863687321 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 249859727374643) ^ 35694246767806 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 249859727374643) ^ 22714520670422 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 249859727374643) ^ 5810691334294 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 249859727374643) ^ 6622 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_307088822935171 : Nat.Prime 307088822935171 := by
  apply lucas_primality 307088822935171 (19 : ZMod 307088822935171)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (541, 1), (24113, 1), (87187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (541, 1), (24113, 1), (87187, 1)] : List FactorBlock).map factorBlockValue).prod) = 307088822935171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_541
      · exact prime_oneHundredTwentyTwoDP_24113
      · exact prime_oneHundredTwentyTwoDP_87187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 307088822935171) ^ 153544411467585 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 307088822935171) ^ 102362940978390 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 307088822935171) ^ 61417764587034 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 307088822935171) ^ 567631835370 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 307088822935171) ^ 12735405090 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (19 : ZMod 307088822935171) ^ 3522185910 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_344692432130789 : Nat.Prime 344692432130789 := by
  apply lucas_primality 344692432130789 (2 : ZMod 344692432130789)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (647918105509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (647918105509, 1)] : List FactorBlock).map factorBlockValue).prod) = 344692432130789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_647918105509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 344692432130789) ^ 172346216065394 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 344692432130789) ^ 49241776018684 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 344692432130789) ^ 18141706954252 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 344692432130789) ^ 532 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_351794961366661 : Nat.Prime 351794961366661 := by
  apply lucas_primality 351794961366661 (2 : ZMod 351794961366661)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (93067450097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (93067450097, 1)] : List FactorBlock).map factorBlockValue).prod) = 351794961366661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_93067450097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 351794961366661) ^ 175897480683330 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 351794961366661) ^ 117264987122220 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 351794961366661) ^ 70358992273332 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 351794961366661) ^ 50256423052380 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 351794961366661) ^ 3780 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_370234221282449 : Nat.Prime 370234221282449 := by
  apply lucas_primality 370234221282449 (3 : ZMod 370234221282449)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (2579, 1), (289429997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (2579, 1), (289429997, 1)] : List FactorBlock).map factorBlockValue).prod) = 370234221282449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_2579
      · exact prime_oneHundredTwentyTwoDP_289429997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 370234221282449) ^ 185117110641224 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 370234221282449) ^ 11943039396208 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 370234221282449) ^ 143557278512 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 370234221282449) ^ 1279184 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_461196675788593 : Nat.Prime 461196675788593 := by
  apply lucas_primality 461196675788593 (5 : ZMod 461196675788593)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2375761, 1), (4044289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2375761, 1), (4044289, 1)] : List FactorBlock).map factorBlockValue).prod) = 461196675788593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_2375761
      · exact prime_oneHundredTwentyTwoDP_4044289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 461196675788593) ^ 230598337894296 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 461196675788593) ^ 153732225262864 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 461196675788593) ^ 194125872 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 461196675788593) ^ 114036528 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_824060139854737 : Nat.Prime 824060139854737 := by
  apply lucas_primality 824060139854737 (5 : ZMod 824060139854737)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (19, 1), (1949, 1), (27271141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (19, 1), (1949, 1), (27271141, 1)] : List FactorBlock).map factorBlockValue).prod) = 824060139854737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_1949
      · exact prime_oneHundredTwentyTwoDP_27271141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 824060139854737) ^ 412030069927368 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 824060139854737) ^ 274686713284912 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 824060139854737) ^ 48474125873808 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 824060139854737) ^ 43371586308144 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 824060139854737) ^ 422811770064 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 824060139854737) ^ 30217296 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1436211617774767 : Nat.Prime 1436211617774767 := by
  apply lucas_primality 1436211617774767 (5 : ZMod 1436211617774767)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (61, 1), (560582208343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (61, 1), (560582208343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1436211617774767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_61
      · exact prime_oneHundredTwentyTwoDP_560582208343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1436211617774767) ^ 718105808887383 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1436211617774767) ^ 478737205924922 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1436211617774767) ^ 205173088253538 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1436211617774767) ^ 23544452750406 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1436211617774767) ^ 2562 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2408418571523641 : Nat.Prime 2408418571523641 := by
  apply lucas_primality 2408418571523641 (7 : ZMod 2408418571523641)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (43, 1), (149, 1), (251, 1), (960017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (43, 1), (149, 1), (251, 1), (960017, 1)] : List FactorBlock).map factorBlockValue).prod) = 2408418571523641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_43
      · exact prime_oneHundredTwentyTwoDP_149
      · exact prime_oneHundredTwentyTwoDP_251
      · exact prime_oneHundredTwentyTwoDP_960017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2408418571523641) ^ 1204209285761820 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2408418571523641) ^ 802806190507880 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2408418571523641) ^ 481683714304728 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2408418571523641) ^ 185262967040280 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2408418571523641) ^ 56009734221480 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2408418571523641) ^ 16163883030360 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2408418571523641) ^ 9595293113640 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2408418571523641) ^ 2508724920 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2884220065465243 : Nat.Prime 2884220065465243 := by
  apply lucas_primality 2884220065465243 (3 : ZMod 2884220065465243)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (659, 1), (5484538481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (659, 1), (5484538481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2884220065465243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_659
      · exact prime_oneHundredTwentyTwoDP_5484538481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2884220065465243) ^ 1442110032732621 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884220065465243) ^ 961406688488414 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884220065465243) ^ 412031437923606 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884220065465243) ^ 151801056077118 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884220065465243) ^ 4376661707838 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884220065465243) ^ 525882 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3225330312651451 : Nat.Prime 3225330312651451 := by
  apply lucas_primality 3225330312651451 (2 : ZMod 3225330312651451)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (47, 1), (2693, 1), (3491, 1), (5407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (47, 1), (2693, 1), (3491, 1), (5407, 1)] : List FactorBlock).map factorBlockValue).prod) = 3225330312651451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_47
      · exact prime_oneHundredTwentyTwoDP_2693
      · exact prime_oneHundredTwentyTwoDP_3491
      · exact prime_oneHundredTwentyTwoDP_5407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3225330312651451) ^ 1612665156325725 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3225330312651451) ^ 1075110104217150 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3225330312651451) ^ 645066062530290 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3225330312651451) ^ 68624049205350 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3225330312651451) ^ 1197671857650 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3225330312651451) ^ 923898685950 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3225330312651451) ^ 596510137350 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_4132857927910693 : Nat.Prime 4132857927910693 := by
  apply lucas_primality 4132857927910693 (5 : ZMod 4132857927910693)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (11876028528479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (11876028528479, 1)] : List FactorBlock).map factorBlockValue).prod) = 4132857927910693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_29
      · exact prime_oneHundredTwentyTwoDP_11876028528479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4132857927910693) ^ 2066428963955346 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4132857927910693) ^ 1377619309303564 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4132857927910693) ^ 142512342341748 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4132857927910693) ^ 348 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_4141689618534647 : Nat.Prime 4141689618534647 := by
  apply lucas_primality 4141689618534647 (5 : ZMod 4141689618534647)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (649183, 1), (43697597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (649183, 1), (43697597, 1)] : List FactorBlock).map factorBlockValue).prod) = 4141689618534647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_73
      · exact prime_oneHundredTwentyTwoDP_649183
      · exact prime_oneHundredTwentyTwoDP_43697597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4141689618534647) ^ 2070844809267323 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4141689618534647) ^ 56735474226502 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4141689618534647) ^ 6379849162 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 4141689618534647) ^ 94780718 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_4702524660656191 : Nat.Prime 4702524660656191 := by
  apply lucas_primality 4702524660656191 (3 : ZMod 4702524660656191)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (89, 1), (587081730419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (89, 1), (587081730419, 1)] : List FactorBlock).map factorBlockValue).prod) = 4702524660656191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_89
      · exact prime_oneHundredTwentyTwoDP_587081730419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4702524660656191) ^ 2351262330328095 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4702524660656191) ^ 1567508220218730 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4702524660656191) ^ 940504932131238 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4702524660656191) ^ 52837355737710 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4702524660656191) ^ 8010 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_5195219319309913 : Nat.Prime 5195219319309913 := by
  apply lucas_primality 5195219319309913 (5 : ZMod 5195219319309913)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (71, 1), (463, 1), (4027, 1), (39883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (71, 1), (463, 1), (4027, 1), (39883, 1)] : List FactorBlock).map factorBlockValue).prod) = 5195219319309913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_41
      · exact prime_oneHundredTwentyTwoDP_71
      · exact prime_oneHundredTwentyTwoDP_463
      · exact prime_oneHundredTwentyTwoDP_4027
      · exact prime_oneHundredTwentyTwoDP_39883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5195219319309913) ^ 2597609659654956 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5195219319309913) ^ 1731739773103304 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5195219319309913) ^ 126712666324632 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5195219319309913) ^ 73172103088872 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5195219319309913) ^ 11220776067624 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5195219319309913) ^ 1290096677256 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5195219319309913) ^ 130261497864 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_5581772233681183 : Nat.Prime 5581772233681183 := by
  apply lucas_primality 5581772233681183 (3 : ZMod 5581772233681183)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (11, 1), (4159, 1), (414995297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (11, 1), (4159, 1), (414995297, 1)] : List FactorBlock).map factorBlockValue).prod) = 5581772233681183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_4159
      · exact prime_oneHundredTwentyTwoDP_414995297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5581772233681183) ^ 2790886116840591 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5581772233681183) ^ 1860590744560394 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5581772233681183) ^ 797396033383026 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5581772233681183) ^ 507433839425562 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5581772233681183) ^ 1342094790498 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5581772233681183) ^ 13450206 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_7942264872169021 : Nat.Prime 7942264872169021 := by
  apply lucas_primality 7942264872169021 (6 : ZMod 7942264872169021)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (7786534188401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (7786534188401, 1)] : List FactorBlock).map factorBlockValue).prod) = 7942264872169021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_7786534188401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7942264872169021) ^ 3971132436084510 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7942264872169021) ^ 2647421624056340 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7942264872169021) ^ 1588452974433804 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7942264872169021) ^ 467192051304060 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (6 : ZMod 7942264872169021) ^ 1020 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_8024208162654569 : Nat.Prime 8024208162654569 := by
  apply lucas_primality 8024208162654569 (3 : ZMod 8024208162654569)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (141107, 1), (374119237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (141107, 1), (374119237, 1)] : List FactorBlock).map factorBlockValue).prod) = 8024208162654569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_141107
      · exact prime_oneHundredTwentyTwoDP_374119237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8024208162654569) ^ 4012104081327284 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8024208162654569) ^ 422326745402872 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8024208162654569) ^ 56866124024 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8024208162654569) ^ 21448264 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_9621419879195303 : Nat.Prime 9621419879195303 := by
  apply lucas_primality 9621419879195303 (5 : ZMod 9621419879195303)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (151, 1), (1385174183587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (151, 1), (1385174183587, 1)] : List FactorBlock).map factorBlockValue).prod) = 9621419879195303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_23
      · exact prime_oneHundredTwentyTwoDP_151
      · exact prime_oneHundredTwentyTwoDP_1385174183587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9621419879195303) ^ 4810709939597651 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 9621419879195303) ^ 418322603443274 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 9621419879195303) ^ 63718012445002 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 9621419879195303) ^ 6946 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_12266960018617519 : Nat.Prime 12266960018617519 := by
  apply lucas_primality 12266960018617519 (13 : ZMod 12266960018617519)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (67, 1), (500243047819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (67, 1), (500243047819, 1)] : List FactorBlock).map factorBlockValue).prod) = 12266960018617519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_61
      · exact prime_oneHundredTwentyTwoDP_67
      · exact prime_oneHundredTwentyTwoDP_500243047819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 12266960018617519) ^ 6133480009308759 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 12266960018617519) ^ 4088986672872506 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 12266960018617519) ^ 201097705223238 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 12266960018617519) ^ 183088955501754 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 12266960018617519) ^ 24522 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_16515945896078807 : Nat.Prime 16515945896078807 := by
  apply lucas_primality 16515945896078807 (5 : ZMod 16515945896078807)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (491, 1), (454558977709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (491, 1), (454558977709, 1)] : List FactorBlock).map factorBlockValue).prod) = 16515945896078807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_37
      · exact prime_oneHundredTwentyTwoDP_491
      · exact prime_oneHundredTwentyTwoDP_454558977709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16515945896078807) ^ 8257972948039403 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16515945896078807) ^ 446376916110238 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16515945896078807) ^ 33637364350466 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16515945896078807) ^ 36334 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_19486271086154021 : Nat.Prime 19486271086154021 := by
  apply lucas_primality 19486271086154021 (2 : ZMod 19486271086154021)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (26332798765073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (26332798765073, 1)] : List FactorBlock).map factorBlockValue).prod) = 19486271086154021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_37
      · exact prime_oneHundredTwentyTwoDP_26332798765073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19486271086154021) ^ 9743135543077010 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 19486271086154021) ^ 3897254217230804 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 19486271086154021) ^ 526655975301460 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 19486271086154021) ^ 740 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_34164726430140893 : Nat.Prime 34164726430140893 := by
  apply lucas_primality 34164726430140893 (2 : ZMod 34164726430140893)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103, 1), (82924093277041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103, 1), (82924093277041, 1)] : List FactorBlock).map factorBlockValue).prod) = 34164726430140893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_103
      · exact prime_oneHundredTwentyTwoDP_82924093277041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34164726430140893) ^ 17082363215070446 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34164726430140893) ^ 331696373108164 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34164726430140893) ^ 412 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_36137177767103869 : Nat.Prime 36137177767103869 := by
  apply lucas_primality 36137177767103869 (10 : ZMod 36137177767103869)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 1), (17, 1), (648875561429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 1), (17, 1), (648875561429, 1)] : List FactorBlock).map factorBlockValue).prod) = 36137177767103869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_648875561429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 36137177767103869) ^ 18068588883551934 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 36137177767103869) ^ 12045725922367956 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 36137177767103869) ^ 5162453966729124 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 36137177767103869) ^ 2779782905161836 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 36137177767103869) ^ 2125716339241404 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 36137177767103869) ^ 55692 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_37515617346431291 : Nat.Prime 37515617346431291 := by
  apply lucas_primality 37515617346431291 (2 : ZMod 37515617346431291)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (31, 1), (12227, 1), (13399, 1), (67153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (31, 1), (12227, 1), (13399, 1), (67153, 1)] : List FactorBlock).map factorBlockValue).prod) = 37515617346431291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_12227
      · exact prime_oneHundredTwentyTwoDP_13399
      · exact prime_oneHundredTwentyTwoDP_67153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37515617346431291) ^ 18757808673215645 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37515617346431291) ^ 7503123469286258 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37515617346431291) ^ 3410510667857390 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37515617346431291) ^ 1210181204723590 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37515617346431291) ^ 3068260190270 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37515617346431291) ^ 2799881882710 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37515617346431291) ^ 558658843930 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_46147521047443889 : Nat.Prime 46147521047443889 := by
  apply lucas_primality 46147521047443889 (3 : ZMod 46147521047443889)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2884220065465243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2884220065465243, 1)] : List FactorBlock).map factorBlockValue).prod) = 46147521047443889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_2884220065465243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 46147521047443889) ^ 23073760523721944 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46147521047443889) ^ 16 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_50315673150460889 : Nat.Prime 50315673150460889 := by
  apply lucas_primality 50315673150460889 (3 : ZMod 50315673150460889)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (73, 1), (86156974572707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (73, 1), (86156974572707, 1)] : List FactorBlock).map factorBlockValue).prod) = 50315673150460889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_73
      · exact prime_oneHundredTwentyTwoDP_86156974572707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 50315673150460889) ^ 25157836575230444 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 50315673150460889) ^ 689255796581656 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 50315673150460889) ^ 584 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_93446343709366019 : Nat.Prime 93446343709366019 := by
  apply lucas_primality 93446343709366019 (2 : ZMod 93446343709366019)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (83, 1), (97, 1), (5351, 1), (8154473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (83, 1), (97, 1), (5351, 1), (8154473, 1)] : List FactorBlock).map factorBlockValue).prod) = 93446343709366019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_83
      · exact prime_oneHundredTwentyTwoDP_97
      · exact prime_oneHundredTwentyTwoDP_5351
      · exact prime_oneHundredTwentyTwoDP_8154473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93446343709366019) ^ 46723171854683009 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93446343709366019) ^ 13349477672766574 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93446343709366019) ^ 4918228616282422 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93446343709366019) ^ 1125859562763446 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93446343709366019) ^ 963364368137794 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93446343709366019) ^ 17463342124718 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 93446343709366019) ^ 11459519666 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_103717763492511673 : Nat.Prime 103717763492511673 := by
  apply lucas_primality 103717763492511673 (10 : ZMod 103717763492511673)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (17, 1), (12105247839929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (17, 1), (12105247839929, 1)] : List FactorBlock).map factorBlockValue).prod) = 103717763492511673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_12105247839929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 103717763492511673) ^ 51858881746255836 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 103717763492511673) ^ 34572587830837224 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 103717763492511673) ^ 14816823356073096 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 103717763492511673) ^ 6101044911324216 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 103717763492511673) ^ 8568 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_121178493845523377 : Nat.Prime 121178493845523377 := by
  apply lucas_primality 121178493845523377 (3 : ZMod 121178493845523377)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3821, 1), (1053953, 1), (1880647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3821, 1), (1053953, 1), (1880647, 1)] : List FactorBlock).map factorBlockValue).prod) = 121178493845523377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3821
      · exact prime_oneHundredTwentyTwoDP_1053953
      · exact prime_oneHundredTwentyTwoDP_1880647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 121178493845523377) ^ 60589246922761688 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 121178493845523377) ^ 31713816761456 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 121178493845523377) ^ 114975234992 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 121178493845523377) ^ 64434470608 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_170309499548514631 : Nat.Prime 170309499548514631 := by
  apply lucas_primality 170309499548514631 (13 : ZMod 170309499548514631)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (6961, 1), (815541347261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (6961, 1), (815541347261, 1)] : List FactorBlock).map factorBlockValue).prod) = 170309499548514631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_6961
      · exact prime_oneHundredTwentyTwoDP_815541347261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 170309499548514631) ^ 85154749774257315 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 170309499548514631) ^ 56769833182838210 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 170309499548514631) ^ 34061899909702926 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 170309499548514631) ^ 24466240417830 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (13 : ZMod 170309499548514631) ^ 208830 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_345894622271962301 : Nat.Prime 345894622271962301 := by
  apply lucas_primality 345894622271962301 (2 : ZMod 345894622271962301)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (23, 1), (29, 1), (5185826420869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (23, 1), (29, 1), (5185826420869, 1)] : List FactorBlock).map factorBlockValue).prod) = 345894622271962301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_23
      · exact prime_oneHundredTwentyTwoDP_29
      · exact prime_oneHundredTwentyTwoDP_5185826420869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 345894622271962301) ^ 172947311135981150 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 345894622271962301) ^ 69178924454392460 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 345894622271962301) ^ 15038896620520100 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 345894622271962301) ^ 11927400767998700 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 345894622271962301) ^ 66700 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_347449971587835313 : Nat.Prime 347449971587835313 := by
  apply lucas_primality 347449971587835313 (10 : ZMod 347449971587835313)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (344692432130789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (344692432130789, 1)] : List FactorBlock).map factorBlockValue).prod) = 347449971587835313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_344692432130789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 347449971587835313) ^ 173724985793917656 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 347449971587835313) ^ 115816657195945104 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 347449971587835313) ^ 49635710226833616 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 347449971587835313) ^ 1008 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_425509391271644473 : Nat.Prime 425509391271644473 := by
  apply lucas_primality 425509391271644473 (5 : ZMod 425509391271644473)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (67, 1), (137, 1), (148579600339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (67, 1), (137, 1), (148579600339, 1)] : List FactorBlock).map factorBlockValue).prod) = 425509391271644473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_67
      · exact prime_oneHundredTwentyTwoDP_137
      · exact prime_oneHundredTwentyTwoDP_148579600339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 425509391271644473) ^ 212754695635822236 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 425509391271644473) ^ 141836463757214824 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 425509391271644473) ^ 32731491636280344 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 425509391271644473) ^ 6350886436890216 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 425509391271644473) ^ 3105907965486456 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 425509391271644473) ^ 2863848 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_995044309510876399 : Nat.Prime 995044309510876399 := by
  apply lucas_primality 995044309510876399 (3 : ZMod 995044309510876399)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (103, 1), (178900451188579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (103, 1), (178900451188579, 1)] : List FactorBlock).map factorBlockValue).prod) = 995044309510876399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_103
      · exact prime_oneHundredTwentyTwoDP_178900451188579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 995044309510876399) ^ 497522154755438199 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 995044309510876399) ^ 331681436503625466 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 995044309510876399) ^ 9660624364183266 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 995044309510876399) ^ 5562 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1365445429804229339 : Nat.Prime 1365445429804229339 := by
  apply lucas_primality 1365445429804229339 (2 : ZMod 1365445429804229339)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1693, 1), (21224320418507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1693, 1), (21224320418507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1365445429804229339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_1693
      · exact prime_oneHundredTwentyTwoDP_21224320418507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1365445429804229339) ^ 682722714902114669 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1365445429804229339) ^ 71865548937064702 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1365445429804229339) ^ 806524175903266 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1365445429804229339) ^ 64334 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_101
      · exact prime_oneHundredTwentyTwoDP_191
      · exact prime_oneHundredTwentyTwoDP_48017
      · exact prime_oneHundredTwentyTwoDP_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2242712249024784457 : Nat.Prime 2242712249024784457 := by
  apply lucas_primality 2242712249024784457 (10 : ZMod 2242712249024784457)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (93446343709366019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (93446343709366019, 1)] : List FactorBlock).map factorBlockValue).prod) = 2242712249024784457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_93446343709366019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 2242712249024784457) ^ 1121356124512392228 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2242712249024784457) ^ 747570749674928152 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 2242712249024784457) ^ 24 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2390062169917025629 : Nat.Prime 2390062169917025629 := by
  apply lucas_primality 2390062169917025629 (2 : ZMod 2390062169917025629)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (631, 1), (16612882433321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (631, 1), (16612882433321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2390062169917025629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_19
      · exact prime_oneHundredTwentyTwoDP_631
      · exact prime_oneHundredTwentyTwoDP_16612882433321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2390062169917025629) ^ 1195031084958512814 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2390062169917025629) ^ 796687389972341876 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2390062169917025629) ^ 125792745785106612 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2390062169917025629) ^ 3787737194797188 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2390062169917025629) ^ 143868 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2483600521622429411 : Nat.Prime 2483600521622429411 := by
  apply lucas_primality 2483600521622429411 (2 : ZMod 2483600521622429411)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (62351, 1), (3983256919091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (62351, 1), (3983256919091, 1)] : List FactorBlock).map factorBlockValue).prod) = 2483600521622429411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_62351
      · exact prime_oneHundredTwentyTwoDP_3983256919091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2483600521622429411) ^ 1241800260811214705 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2483600521622429411) ^ 496720104324485882 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2483600521622429411) ^ 39832569190910 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2483600521622429411) ^ 623510 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_5021538316451439859 : Nat.Prime 5021538316451439859 := by
  apply lucas_primality 5021538316451439859 (2 : ZMod 5021538316451439859)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (11246699, 1), (370223857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (11246699, 1), (370223857, 1)] : List FactorBlock).map factorBlockValue).prod) = 5021538316451439859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_67
      · exact prime_oneHundredTwentyTwoDP_11246699
      · exact prime_oneHundredTwentyTwoDP_370223857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5021538316451439859) ^ 2510769158225719929 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5021538316451439859) ^ 1673846105483813286 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5021538316451439859) ^ 74948333081364774 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5021538316451439859) ^ 446489971542 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5021538316451439859) ^ 13563518994 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_6472055515108145239 : Nat.Prime 6472055515108145239 := by
  apply lucas_primality 6472055515108145239 (3 : ZMod 6472055515108145239)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (29, 1), (4132857927910693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (29, 1), (4132857927910693, 1)] : List FactorBlock).map factorBlockValue).prod) = 6472055515108145239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_29
      · exact prime_oneHundredTwentyTwoDP_4132857927910693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6472055515108145239) ^ 3236027757554072619 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6472055515108145239) ^ 2157351838369381746 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6472055515108145239) ^ 223174328107177422 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6472055515108145239) ^ 1566 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_6553450429077335947 : Nat.Prime 6553450429077335947 := by
  apply lucas_primality 6553450429077335947 (2 : ZMod 6553450429077335947)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (997, 1), (1102861, 1), (13607551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (997, 1), (1102861, 1), (13607551, 1)] : List FactorBlock).map factorBlockValue).prod) = 6553450429077335947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_73
      · exact prime_oneHundredTwentyTwoDP_997
      · exact prime_oneHundredTwentyTwoDP_1102861
      · exact prime_oneHundredTwentyTwoDP_13607551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6553450429077335947) ^ 3276725214538667973 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6553450429077335947) ^ 2184483476359111982 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6553450429077335947) ^ 89773293549004602 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6553450429077335947) ^ 6573169938894018 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6553450429077335947) ^ 5942227015986 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6553450429077335947) ^ 481603958646 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_6584054627187640553 : Nat.Prime 6584054627187640553 := by
  apply lucas_primality 6584054627187640553 (3 : ZMod 6584054627187640553)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (229, 1), (115932783265031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (229, 1), (115932783265031, 1)] : List FactorBlock).map factorBlockValue).prod) = 6584054627187640553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_31
      · exact prime_oneHundredTwentyTwoDP_229
      · exact prime_oneHundredTwentyTwoDP_115932783265031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6584054627187640553) ^ 3292027313593820276 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6584054627187640553) ^ 212388858941536792 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6584054627187640553) ^ 28751330249727688 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6584054627187640553) ^ 56792 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_10791879819095819533 : Nat.Prime 10791879819095819533 := by
  apply lucas_primality 10791879819095819533 (2 : ZMod 10791879819095819533)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (33811, 1), (174599, 1), (13849159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (33811, 1), (174599, 1), (13849159, 1)] : List FactorBlock).map factorBlockValue).prod) = 10791879819095819533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_33811
      · exact prime_oneHundredTwentyTwoDP_174599
      · exact prime_oneHundredTwentyTwoDP_13849159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10791879819095819533) ^ 5395939909547909766 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10791879819095819533) ^ 3597293273031939844 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10791879819095819533) ^ 981079983554165412 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10791879819095819533) ^ 319182509215812 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10791879819095819533) ^ 61809516773268 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10791879819095819533) ^ 779244416148 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_15689175712571554709 : Nat.Prime 15689175712571554709 := by
  apply lucas_primality 15689175712571554709 (2 : ZMod 15689175712571554709)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2731, 1), (1436211617774767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2731, 1), (1436211617774767, 1)] : List FactorBlock).map factorBlockValue).prod) = 15689175712571554709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_2731
      · exact prime_oneHundredTwentyTwoDP_1436211617774767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15689175712571554709) ^ 7844587856285777354 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15689175712571554709) ^ 5744846471099068 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15689175712571554709) ^ 10924 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_27174054035038058327 : Nat.Prime 27174054035038058327 := by
  apply lucas_primality 27174054035038058327 (5 : ZMod 27174054035038058327)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (103717763492511673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (103717763492511673, 1)] : List FactorBlock).map factorBlockValue).prod) = 27174054035038058327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_131
      · exact prime_oneHundredTwentyTwoDP_103717763492511673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 27174054035038058327) ^ 13587027017519029163 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 27174054035038058327) ^ 207435526985023346 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 27174054035038058327) ^ 262 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_27742471165114935421 : Nat.Prime 27742471165114935421 := by
  apply lucas_primality 27742471165114935421 (10 : ZMod 27742471165114935421)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (89, 1), (5195219319309913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (89, 1), (5195219319309913, 1)] : List FactorBlock).map factorBlockValue).prod) = 27742471165114935421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_89
      · exact prime_oneHundredTwentyTwoDP_5195219319309913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 27742471165114935421) ^ 13871235582557467710 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 27742471165114935421) ^ 9247490388371645140 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 27742471165114935421) ^ 5548494233022987084 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 27742471165114935421) ^ 311713159158594780 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 27742471165114935421) ^ 5340 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_51432112573014120209 : Nat.Prime 51432112573014120209 := by
  apply lucas_primality 51432112573014120209 (3 : ZMod 51432112573014120209)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (59, 1), (146519, 1), (21873561509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (59, 1), (146519, 1), (21873561509, 1)] : List FactorBlock).map factorBlockValue).prod) = 51432112573014120209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_59
      · exact prime_oneHundredTwentyTwoDP_146519
      · exact prime_oneHundredTwentyTwoDP_21873561509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51432112573014120209) ^ 25716056286507060104 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51432112573014120209) ^ 3025418386647889424 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51432112573014120209) ^ 871730721576510512 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51432112573014120209) ^ 351026915096432 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51432112573014120209) ^ 2351336912 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_64677584209656769033 : Nat.Prime 64677584209656769033 := by
  apply lucas_primality 64677584209656769033 (10 : ZMod 64677584209656769033)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (7589, 1), (32282362535117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (7589, 1), (32282362535117, 1)] : List FactorBlock).map factorBlockValue).prod) = 64677584209656769033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_7589
      · exact prime_oneHundredTwentyTwoDP_32282362535117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 64677584209656769033) ^ 32338792104828384516 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 64677584209656769033) ^ 21559194736552256344 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 64677584209656769033) ^ 5879780382696069912 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 64677584209656769033) ^ 8522543709270888 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 64677584209656769033) ^ 2003496 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_95705781893674799233 : Nat.Prime 95705781893674799233 := by
  apply lucas_primality 95705781893674799233 (5 : ZMod 95705781893674799233)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (53, 1), (4702524660656191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (53, 1), (4702524660656191, 1)] : List FactorBlock).map factorBlockValue).prod) = 95705781893674799233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_53
      · exact prime_oneHundredTwentyTwoDP_4702524660656191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 95705781893674799233) ^ 47852890946837399616 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 95705781893674799233) ^ 31901927297891599744 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 95705781893674799233) ^ 1805769469691977344 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 95705781893674799233) ^ 20352 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_283648296797652807373 : Nat.Prime 283648296797652807373 := by
  apply lucas_primality 283648296797652807373 (2 : ZMod 283648296797652807373)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (16193, 1), (132702447558547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (16193, 1), (132702447558547, 1)] : List FactorBlock).map factorBlockValue).prod) = 283648296797652807373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_16193
      · exact prime_oneHundredTwentyTwoDP_132702447558547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 283648296797652807373) ^ 141824148398826403686 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 283648296797652807373) ^ 94549432265884269124 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 283648296797652807373) ^ 25786208799786618852 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 283648296797652807373) ^ 17516723077728204 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 283648296797652807373) ^ 2137476 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_512744558079028277813 : Nat.Prime 512744558079028277813 := by
  apply lucas_primality 512744558079028277813 (2 : ZMod 512744558079028277813)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (80233, 1), (207661, 1), (7693661881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (80233, 1), (207661, 1), (7693661881, 1)] : List FactorBlock).map factorBlockValue).prod) = 512744558079028277813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_80233
      · exact prime_oneHundredTwentyTwoDP_207661
      · exact prime_oneHundredTwentyTwoDP_7693661881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 512744558079028277813) ^ 256372279039514138906 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 512744558079028277813) ^ 6390694079481364 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 512744558079028277813) ^ 2469142294793092 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 512744558079028277813) ^ 66645060052 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_877849768061400605441 : Nat.Prime 877849768061400605441 := by
  apply lucas_primality 877849768061400605441 (3 : ZMod 877849768061400605441)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (2153, 1), (8359679, 1), (38104529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (2153, 1), (8359679, 1), (38104529, 1)] : List FactorBlock).map factorBlockValue).prod) = 877849768061400605441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_2153
      · exact prime_oneHundredTwentyTwoDP_8359679
      · exact prime_oneHundredTwentyTwoDP_38104529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 877849768061400605441) ^ 438924884030700302720 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 877849768061400605441) ^ 175569953612280121088 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 877849768061400605441) ^ 407733287534324480 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 877849768061400605441) ^ 105009985199360 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 877849768061400605441) ^ 23037937775360 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1193855472820581666619 : Nat.Prime 1193855472820581666619 := by
  apply lucas_primality 1193855472820581666619 (3 : ZMod 1193855472820581666619)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (28901, 1), (5053897, 1), (20332297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (28901, 1), (5053897, 1), (20332297, 1)] : List FactorBlock).map factorBlockValue).prod) = 1193855472820581666619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_67
      · exact prime_oneHundredTwentyTwoDP_28901
      · exact prime_oneHundredTwentyTwoDP_5053897
      · exact prime_oneHundredTwentyTwoDP_20332297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1193855472820581666619) ^ 596927736410290833309 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1193855472820581666619) ^ 397951824273527222206 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1193855472820581666619) ^ 17818738400307189054 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1193855472820581666619) ^ 41308448594186418 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1193855472820581666619) ^ 236224733669994 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1193855472820581666619) ^ 58717196233194 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1415175506116068922657 : Nat.Prime 1415175506116068922657 := by
  apply lucas_primality 1415175506116068922657 (5 : ZMod 1415175506116068922657)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (83, 1), (12269, 1), (14476107892693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (83, 1), (12269, 1), (14476107892693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1415175506116068922657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_83
      · exact prime_oneHundredTwentyTwoDP_12269
      · exact prime_oneHundredTwentyTwoDP_14476107892693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1415175506116068922657) ^ 707587753058034461328 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1415175506116068922657) ^ 471725168705356307552 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1415175506116068922657) ^ 17050307302603240032 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1415175506116068922657) ^ 115345627688977824 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1415175506116068922657) ^ 97759392 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2179165913426555675971 : Nat.Prime 2179165913426555675971 := by
  apply lucas_primality 2179165913426555675971 (2 : ZMod 2179165913426555675971)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (5861, 1), (9910073, 1), (33800159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (5861, 1), (9910073, 1), (33800159, 1)] : List FactorBlock).map factorBlockValue).prod) = 2179165913426555675971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_37
      · exact prime_oneHundredTwentyTwoDP_5861
      · exact prime_oneHundredTwentyTwoDP_9910073
      · exact prime_oneHundredTwentyTwoDP_33800159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2179165913426555675971) ^ 1089582956713277837985 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179165913426555675971) ^ 726388637808851891990 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179165913426555675971) ^ 435833182685311135194 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179165913426555675971) ^ 58896376038555558810 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179165913426555675971) ^ 371807867842783770 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179165913426555675971) ^ 219894032407890 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179165913426555675971) ^ 64472061016830 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2700111909438818526781 : Nat.Prime 2700111909438818526781 := by
  apply lucas_primality 2700111909438818526781 (2 : ZMod 2700111909438818526781)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (643, 1), (25117, 1), (108041, 1), (8596901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (643, 1), (25117, 1), (108041, 1), (8596901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2700111909438818526781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_643
      · exact prime_oneHundredTwentyTwoDP_25117
      · exact prime_oneHundredTwentyTwoDP_108041
      · exact prime_oneHundredTwentyTwoDP_8596901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2700111909438818526781) ^ 1350055954719409263390 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2700111909438818526781) ^ 900037303146272842260 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2700111909438818526781) ^ 540022381887763705356 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2700111909438818526781) ^ 4199240916701117460 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2700111909438818526781) ^ 107501369966111340 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2700111909438818526781) ^ 24991548666143580 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2700111909438818526781) ^ 314079679344780 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2791863109436682428689 : Nat.Prime 2791863109436682428689 := by
  apply lucas_primality 2791863109436682428689 (7 : ZMod 2791863109436682428689)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (257, 1), (7853, 1), (630871, 1), (1986167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (257, 1), (7853, 1), (630871, 1), (1986167, 1)] : List FactorBlock).map factorBlockValue).prod) = 2791863109436682428689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_23
      · exact prime_oneHundredTwentyTwoDP_257
      · exact prime_oneHundredTwentyTwoDP_7853
      · exact prime_oneHundredTwentyTwoDP_630871
      · exact prime_oneHundredTwentyTwoDP_1986167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2791863109436682428689) ^ 1395931554718341214344 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2791863109436682428689) ^ 930621036478894142896 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2791863109436682428689) ^ 121385352584203583856 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2791863109436682428689) ^ 10863280581465690384 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2791863109436682428689) ^ 355515485729871696 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2791863109436682428689) ^ 4425410439593328 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2791863109436682428689) ^ 1405653758942064 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2842361254928174398637 : Nat.Prime 2842361254928174398637 := by
  apply lucas_primality 2842361254928174398637 (2 : ZMod 2842361254928174398637)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (73, 1), (149, 1), (190465374346769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (73, 1), (149, 1), (190465374346769, 1)] : List FactorBlock).map factorBlockValue).prod) = 2842361254928174398637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_73
      · exact prime_oneHundredTwentyTwoDP_149
      · exact prime_oneHundredTwentyTwoDP_190465374346769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2842361254928174398637) ^ 1421180627464087199318 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2842361254928174398637) ^ 406051607846882056948 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2842361254928174398637) ^ 38936455546961293132 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2842361254928174398637) ^ 19076250033074995964 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2842361254928174398637) ^ 14923244 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3329096539813792250521 : Nat.Prime 3329096539813792250521 := by
  apply lucas_primality 3329096539813792250521 (11 : ZMod 3329096539813792250521)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (27742471165114935421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (27742471165114935421, 1)] : List FactorBlock).map factorBlockValue).prod) = 3329096539813792250521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_27742471165114935421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3329096539813792250521) ^ 1664548269906896125260 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 3329096539813792250521) ^ 1109698846604597416840 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 3329096539813792250521) ^ 665819307962758450104 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 3329096539813792250521) ^ 120 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_14176642172834957319307 : Nat.Prime 14176642172834957319307 := by
  apply lucas_primality 14176642172834957319307 (2 : ZMod 14176642172834957319307)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1423, 1), (50315673150460889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1423, 1), (50315673150460889, 1)] : List FactorBlock).map factorBlockValue).prod) = 14176642172834957319307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_1423
      · exact prime_oneHundredTwentyTwoDP_50315673150460889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14176642172834957319307) ^ 7088321086417478659653 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14176642172834957319307) ^ 4725547390944985773102 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14176642172834957319307) ^ 1288785652075905210846 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14176642172834957319307) ^ 9962503283791256022 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14176642172834957319307) ^ 281754 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_14885255192191900547569 : Nat.Prime 14885255192191900547569 := by
  apply lucas_primality 14885255192191900547569 (11 : ZMod 14885255192191900547569)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (37, 1), (241, 1), (2137, 1), (242453, 1), (67121893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (37, 1), (241, 1), (2137, 1), (242453, 1), (67121893, 1)] : List FactorBlock).map factorBlockValue).prod) = 14885255192191900547569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_37
      · exact prime_oneHundredTwentyTwoDP_241
      · exact prime_oneHundredTwentyTwoDP_2137
      · exact prime_oneHundredTwentyTwoDP_242453
      · exact prime_oneHundredTwentyTwoDP_67121893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14885255192191900547569) ^ 7442627596095950273784 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 14885255192191900547569) ^ 4961751730730633515856 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 14885255192191900547569) ^ 402304194383564879664 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 14885255192191900547569) ^ 61764544365941496048 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 14885255192191900547569) ^ 6965491432939588464 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 14885255192191900547569) ^ 61394394757713456 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (11 : ZMod 14885255192191900547569) ^ 221764532060976 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_24538022910278984811443 : Nat.Prime 24538022910278984811443 := by
  apply lucas_primality 24538022910278984811443 (2 : ZMod 24538022910278984811443)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (691, 1), (1231, 1), (351794961366661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (691, 1), (1231, 1), (351794961366661, 1)] : List FactorBlock).map factorBlockValue).prod) = 24538022910278984811443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_41
      · exact prime_oneHundredTwentyTwoDP_691
      · exact prime_oneHundredTwentyTwoDP_1231
      · exact prime_oneHundredTwentyTwoDP_351794961366661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24538022910278984811443) ^ 12269011455139492405721 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24538022910278984811443) ^ 598488363665341092962 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24538022910278984811443) ^ 35510886990273494662 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24538022910278984811443) ^ 19933406100957745582 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24538022910278984811443) ^ 69750922 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_51282140938425950632433 : Nat.Prime 51282140938425950632433 := by
  apply lucas_primality 51282140938425950632433 (3 : ZMod 51282140938425950632433)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (401, 1), (607, 1), (977, 1), (24917, 1), (540907229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (401, 1), (607, 1), (977, 1), (24917, 1), (540907229, 1)] : List FactorBlock).map factorBlockValue).prod) = 51282140938425950632433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_401
      · exact prime_oneHundredTwentyTwoDP_607
      · exact prime_oneHundredTwentyTwoDP_977
      · exact prime_oneHundredTwentyTwoDP_24917
      · exact prime_oneHundredTwentyTwoDP_540907229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51282140938425950632433) ^ 25641070469212975316216 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51282140938425950632433) ^ 127885638250438779632 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51282140938425950632433) ^ 84484581447159720976 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51282140938425950632433) ^ 52489397071060338416 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51282140938425950632433) ^ 2058118591260021296 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51282140938425950632433) ^ 94807645727408 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_161175455535503625144581 : Nat.Prime 161175455535503625144581 := by
  apply lucas_primality 161175455535503625144581 (2 : ZMod 161175455535503625144581)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59037325643, 1), (136503012103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59037325643, 1), (136503012103, 1)] : List FactorBlock).map factorBlockValue).prod) = 161175455535503625144581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_59037325643
      · exact prime_oneHundredTwentyTwoDP_136503012103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 161175455535503625144581) ^ 80587727767751812572290 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161175455535503625144581) ^ 32235091107100725028916 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161175455535503625144581) ^ 2730060242060 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161175455535503625144581) ^ 1180746512860 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_512021866739596507477409 : Nat.Prime 512021866739596507477409 := by
  apply lucas_primality 512021866739596507477409 (3 : ZMod 512021866739596507477409)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (131, 1), (2729, 1), (935461, 1), (47845160171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (131, 1), (2729, 1), (935461, 1), (47845160171, 1)] : List FactorBlock).map factorBlockValue).prod) = 512021866739596507477409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_131
      · exact prime_oneHundredTwentyTwoDP_2729
      · exact prime_oneHundredTwentyTwoDP_935461
      · exact prime_oneHundredTwentyTwoDP_47845160171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 512021866739596507477409) ^ 256010933369798253738704 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 512021866739596507477409) ^ 3908563868241194713568 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 512021866739596507477409) ^ 187622523539610299552 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 512021866739596507477409) ^ 547347101311114528 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 512021866739596507477409) ^ 10701643905248 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_532077230729241838839857 : Nat.Prime 532077230729241838839857 := by
  apply lucas_primality 532077230729241838839857 (3 : ZMod 532077230729241838839857)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (587, 1), (1019, 1), (7942264872169021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (587, 1), (1019, 1), (7942264872169021, 1)] : List FactorBlock).map factorBlockValue).prod) = 532077230729241838839857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_587
      · exact prime_oneHundredTwentyTwoDP_1019
      · exact prime_oneHundredTwentyTwoDP_7942264872169021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 532077230729241838839857) ^ 266038615364620919419928 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 532077230729241838839857) ^ 76011032961320262691408 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 532077230729241838839857) ^ 906434805330906028688 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 532077230729241838839857) ^ 522156261755880116624 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 532077230729241838839857) ^ 66993136 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_725579812969315734130763 : Nat.Prime 725579812969315734130763 := by
  apply lucas_primality 725579812969315734130763 (2 : ZMod 725579812969315734130763)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (30695257, 1), (132798727962997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (30695257, 1), (132798727962997, 1)] : List FactorBlock).map factorBlockValue).prod) = 725579812969315734130763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_89
      · exact prime_oneHundredTwentyTwoDP_30695257
      · exact prime_oneHundredTwentyTwoDP_132798727962997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 725579812969315734130763) ^ 362789906484657867065381 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 725579812969315734130763) ^ 8152582168194558810458 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 725579812969315734130763) ^ 23638173577413466 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 725579812969315734130763) ^ 5463755746 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_926868914453718656421767 : Nat.Prime 926868914453718656421767 := by
  apply lucas_primality 926868914453718656421767 (5 : ZMod 926868914453718656421767)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (131, 1), (586387, 1), (16981813, 1), (20897759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (131, 1), (586387, 1), (16981813, 1), (20897759, 1)] : List FactorBlock).map factorBlockValue).prod) = 926868914453718656421767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_17
      · exact prime_oneHundredTwentyTwoDP_131
      · exact prime_oneHundredTwentyTwoDP_586387
      · exact prime_oneHundredTwentyTwoDP_16981813
      · exact prime_oneHundredTwentyTwoDP_20897759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 926868914453718656421767) ^ 463434457226859328210883 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 926868914453718656421767) ^ 54521700850218744495398 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 926868914453718656421767) ^ 7075335224837546995586 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 926868914453718656421767) ^ 1580643695125776418 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 926868914453718656421767) ^ 54580091916788782 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 926868914453718656421767) ^ 44352550646876474 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1120954356085148680425467 : Nat.Prime 1120954356085148680425467 := by
  apply lucas_primality 1120954356085148680425467 (2 : ZMod 1120954356085148680425467)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (159695036621, 1), (3509671871473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (159695036621, 1), (3509671871473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1120954356085148680425467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_159695036621
      · exact prime_oneHundredTwentyTwoDP_3509671871473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1120954356085148680425467) ^ 560477178042574340212733 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1120954356085148680425467) ^ 7019343742946 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1120954356085148680425467) ^ 319390073242 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1673006238668248035775931 : Nat.Prime 1673006238668248035775931 := by
  apply lucas_primality 1673006238668248035775931 (2 : ZMod 1673006238668248035775931)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (21349571, 1), (159923515384067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (21349571, 1), (159923515384067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1673006238668248035775931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_21349571
      · exact prime_oneHundredTwentyTwoDP_159923515384067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1673006238668248035775931) ^ 836503119334124017887965 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673006238668248035775931) ^ 334601247733649607155186 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673006238668248035775931) ^ 239000891238321147967990 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673006238668248035775931) ^ 78362522538192830 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673006238668248035775931) ^ 10461289790 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2268262747653593171089121 : Nat.Prime 2268262747653593171089121 := by
  apply lucas_primality 2268262747653593171089121 (3 : ZMod 2268262747653593171089121)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (14176642172834957319307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (14176642172834957319307, 1)] : List FactorBlock).map factorBlockValue).prod) = 2268262747653593171089121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_14176642172834957319307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2268262747653593171089121) ^ 1134131373826796585544560 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2268262747653593171089121) ^ 453652549530718634217824 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2268262747653593171089121) ^ 160 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_3953744685193507199813221 : Nat.Prime 3953744685193507199813221 := by
  apply lucas_primality 3953744685193507199813221 (10 : ZMod 3953744685193507199813221)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (113, 1), (809, 1), (1609, 1), (34461248638483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (113, 1), (809, 1), (1609, 1), (34461248638483, 1)] : List FactorBlock).map factorBlockValue).prod) = 3953744685193507199813221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_113
      · exact prime_oneHundredTwentyTwoDP_809
      · exact prime_oneHundredTwentyTwoDP_1609
      · exact prime_oneHundredTwentyTwoDP_34461248638483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3953744685193507199813221) ^ 1976872342596753599906610 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3953744685193507199813221) ^ 1317914895064502399937740 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3953744685193507199813221) ^ 790748937038701439962644 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3953744685193507199813221) ^ 304134206553346707677940 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3953744685193507199813221) ^ 34988891019411568139940 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3953744685193507199813221) ^ 4887199858088389616580 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3953744685193507199813221) ^ 2457268294091676320580 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3953744685193507199813221) ^ 114730163340 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_4364720688148167286702963 : Nat.Prime 4364720688148167286702963 := by
  apply lucas_primality 4364720688148167286702963 (2 : ZMod 4364720688148167286702963)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (4583, 1), (212512073, 1), (6072487511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (4583, 1), (212512073, 1), (6072487511, 1)] : List FactorBlock).map factorBlockValue).prod) = 4364720688148167286702963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_41
      · exact prime_oneHundredTwentyTwoDP_4583
      · exact prime_oneHundredTwentyTwoDP_212512073
      · exact prime_oneHundredTwentyTwoDP_6072487511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4364720688148167286702963) ^ 2182360344074083643351481 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4364720688148167286702963) ^ 1454906896049389095567654 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4364720688148167286702963) ^ 106456602149955299675682 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4364720688148167286702963) ^ 952371959011164583614 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4364720688148167286702963) ^ 20538695174029794 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4364720688148167286702963) ^ 718769808952542 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_16274011041469517788151429 : Nat.Prime 16274011041469517788151429 := by
  apply lucas_primality 16274011041469517788151429 (2 : ZMod 16274011041469517788151429)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1867, 1), (2179165913426555675971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1867, 1), (2179165913426555675971, 1)] : List FactorBlock).map factorBlockValue).prod) = 16274011041469517788151429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_1867
      · exact prime_oneHundredTwentyTwoDP_2179165913426555675971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16274011041469517788151429) ^ 8137005520734758894075714 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 16274011041469517788151429) ^ 8716663653706222703884 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 16274011041469517788151429) ^ 7468 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_126080908969007286849987863 : Nat.Prime 126080908969007286849987863 := by
  apply lucas_primality 126080908969007286849987863 (5 : ZMod 126080908969007286849987863)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1247303643827, 1), (50541385649353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1247303643827, 1), (50541385649353, 1)] : List FactorBlock).map factorBlockValue).prod) = 126080908969007286849987863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_1247303643827
      · exact prime_oneHundredTwentyTwoDP_50541385649353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 126080908969007286849987863) ^ 63040454484503643424993931 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 126080908969007286849987863) ^ 101082771298706 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 126080908969007286849987863) ^ 2494607287654 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_147180163123004424649373587 : Nat.Prime 147180163123004424649373587 := by
  apply lucas_primality 147180163123004424649373587 (5 : ZMod 147180163123004424649373587)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (607, 1), (116833, 1), (345894622271962301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (607, 1), (116833, 1), (345894622271962301, 1)] : List FactorBlock).map factorBlockValue).prod) = 147180163123004424649373587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_607
      · exact prime_oneHundredTwentyTwoDP_116833
      · exact prime_oneHundredTwentyTwoDP_345894622271962301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 147180163123004424649373587) ^ 73590081561502212324686793 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 147180163123004424649373587) ^ 49060054374334808216457862 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 147180163123004424649373587) ^ 242471438423401029076398 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 147180163123004424649373587) ^ 1259748214314486700242 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 147180163123004424649373587) ^ 425505786 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_629853973190149939547537621 : Nat.Prime 629853973190149939547537621 := by
  apply lucas_primality 629853973190149939547537621 (3 : ZMod 629853973190149939547537621)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (113, 1), (6047, 1), (6584054627187640553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (113, 1), (6047, 1), (6584054627187640553, 1)] : List FactorBlock).map factorBlockValue).prod) = 629853973190149939547537621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_113
      · exact prime_oneHundredTwentyTwoDP_6047
      · exact prime_oneHundredTwentyTwoDP_6584054627187640553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 629853973190149939547537621) ^ 314926986595074969773768810 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 629853973190149939547537621) ^ 125970794638029987909507524 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 629853973190149939547537621) ^ 89979139027164277078219660 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 629853973190149939547537621) ^ 5573928966284512739358740 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 629853973190149939547537621) ^ 104159744202108473548460 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 629853973190149939547537621) ^ 95663540 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_930558450713189265525071711 : Nat.Prime 930558450713189265525071711 := by
  apply lucas_primality 930558450713189265525071711 (21 : ZMod 930558450713189265525071711)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2381625691, 1), (5581772233681183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2381625691, 1), (5581772233681183, 1)] : List FactorBlock).map factorBlockValue).prod) = 930558450713189265525071711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_2381625691
      · exact prime_oneHundredTwentyTwoDP_5581772233681183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 930558450713189265525071711) ^ 465279225356594632762535855 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (21 : ZMod 930558450713189265525071711) ^ 186111690142637853105014342 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (21 : ZMod 930558450713189265525071711) ^ 132936921530455609360724530 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (21 : ZMod 930558450713189265525071711) ^ 390724056357682810 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (21 : ZMod 930558450713189265525071711) ^ 166713798370 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_1534431487878131235706235269 : Nat.Prime 1534431487878131235706235269 := by
  apply lucas_primality 1534431487878131235706235269 (2 : ZMod 1534431487878131235706235269)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1201, 1), (102677, 1), (237409, 1), (1455900328741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1201, 1), (102677, 1), (237409, 1), (1455900328741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1534431487878131235706235269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_1201
      · exact prime_oneHundredTwentyTwoDP_102677
      · exact prime_oneHundredTwentyTwoDP_237409
      · exact prime_oneHundredTwentyTwoDP_1455900328741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1534431487878131235706235269) ^ 767215743939065617853117634 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1534431487878131235706235269) ^ 511477162626043745235411756 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1534431487878131235706235269) ^ 1277628216384788705833668 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1534431487878131235706235269) ^ 14944257115791571975284 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1534431487878131235706235269) ^ 6463240601148782210052 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1534431487878131235706235269) ^ 1053939928157748 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_2486837238974902347523898539 : Nat.Prime 2486837238974902347523898539 := by
  apply lucas_primality 2486837238974902347523898539 (3 : ZMod 2486837238974902347523898539)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (683, 1), (105200659, 1), (824060139854737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (683, 1), (105200659, 1), (824060139854737, 1)] : List FactorBlock).map factorBlockValue).prod) = 2486837238974902347523898539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_683
      · exact prime_oneHundredTwentyTwoDP_105200659
      · exact prime_oneHundredTwentyTwoDP_824060139854737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2486837238974902347523898539) ^ 1243418619487451173761949269 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486837238974902347523898539) ^ 828945746324967449174632846 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486837238974902347523898539) ^ 355262462710700335360556934 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486837238974902347523898539) ^ 3641050130270720860210686 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486837238974902347523898539) ^ 23638989171872985582 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486837238974902347523898539) ^ 3017786104074 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_24039426643424056026064352537 : Nat.Prime 24039426643424056026064352537 := by
  apply lucas_primality 24039426643424056026064352537 (3 : ZMod 24039426643424056026064352537)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (41, 1), (109, 1), (673, 1), (1164659, 1), (1467043, 1), (15803939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (41, 1), (109, 1), (673, 1), (1164659, 1), (1467043, 1), (15803939, 1)] : List FactorBlock).map factorBlockValue).prod) = 24039426643424056026064352537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_37
      · exact prime_oneHundredTwentyTwoDP_41
      · exact prime_oneHundredTwentyTwoDP_109
      · exact prime_oneHundredTwentyTwoDP_673
      · exact prime_oneHundredTwentyTwoDP_1164659
      · exact prime_oneHundredTwentyTwoDP_1467043
      · exact prime_oneHundredTwentyTwoDP_15803939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24039426643424056026064352537) ^ 12019713321712028013032176268 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24039426643424056026064352537) ^ 649714233606055568272009528 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24039426643424056026064352537) ^ 586327479107903805513764696 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24039426643424056026064352537) ^ 220545198563523449780406904 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24039426643424056026064352537) ^ 35719801847584035699947032 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24039426643424056026064352537) ^ 20640742606569009492104 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24039426643424056026064352537) ^ 16386313586871043334152 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 24039426643424056026064352537) ^ 1521103482076465622024 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_48078853286848112052128705077 : Nat.Prime 48078853286848112052128705077 := by
  apply lucas_primality 48078853286848112052128705077 (5 : ZMod 48078853286848112052128705077)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (78929, 1), (512744558079028277813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (78929, 1), (512744558079028277813, 1)] : List FactorBlock).map factorBlockValue).prod) = 48078853286848112052128705077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_78929
      · exact prime_oneHundredTwentyTwoDP_512744558079028277813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 48078853286848112052128705077) ^ 24039426643424056026064352538 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48078853286848112052128705077) ^ 16026284428949370684042901692 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48078853286848112052128705077) ^ 4370804844258919277466245916 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48078853286848112052128705077) ^ 609140534997885594041844 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48078853286848112052128705077) ^ 93767652 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_72118279930272168078193057639 : Nat.Prime 72118279930272168078193057639 := by
  apply lucas_primality 72118279930272168078193057639 (3 : ZMod 72118279930272168078193057639)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (859, 1), (30339944179, 1), (461196675788593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (859, 1), (30339944179, 1), (461196675788593, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118279930272168078193057639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_859
      · exact prime_oneHundredTwentyTwoDP_30339944179
      · exact prime_oneHundredTwentyTwoDP_461196675788593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72118279930272168078193057639) ^ 36059139965136084039096528819 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272168078193057639) ^ 24039426643424056026064352546 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272168078193057639) ^ 83956088393797634549700882 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272168078193057639) ^ 2377007667014408322 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (3 : ZMod 72118279930272168078193057639) ^ 156372072298566 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_144236559860544336156386115203 : Nat.Prime 144236559860544336156386115203 := by
  apply lucas_primality 144236559860544336156386115203 (2 : ZMod 144236559860544336156386115203)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (97, 1), (211, 1), (112199, 1), (1365445429804229339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (97, 1), (211, 1), (112199, 1), (1365445429804229339, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_23
      · exact prime_oneHundredTwentyTwoDP_97
      · exact prime_oneHundredTwentyTwoDP_211
      · exact prime_oneHundredTwentyTwoDP_112199
      · exact prime_oneHundredTwentyTwoDP_1365445429804229339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 144236559860544336156386115203) ^ 72118279930272168078193057601 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115203) ^ 6271154776545405919842874574 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115203) ^ 1486974843923137486148310466 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115203) ^ 683585591756134294580028982 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115203) ^ 1285542294142945446540398 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115203) ^ 105633338918 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_144236559860544336156386115221 : Nat.Prime 144236559860544336156386115221 := by
  apply lucas_primality 144236559860544336156386115221 (2 : ZMod 144236559860544336156386115221)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (1031, 1), (1549, 1), (76480009, 1), (4541967206407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (1031, 1), (1549, 1), (76480009, 1), (4541967206407, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_13
      · exact prime_oneHundredTwentyTwoDP_1031
      · exact prime_oneHundredTwentyTwoDP_1549
      · exact prime_oneHundredTwentyTwoDP_76480009
      · exact prime_oneHundredTwentyTwoDP_4541967206407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 144236559860544336156386115221) ^ 72118279930272168078193057610 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115221) ^ 28847311972108867231277223044 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115221) ^ 11095119989272641242798931940 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115221) ^ 139899670087821858541596620 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115221) ^ 93115919858324297066743780 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115221) ^ 1885938060762314190580 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115221) ^ 31756407148224460 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_144236559860544336156386115251 : Nat.Prime 144236559860544336156386115251 := by
  apply lucas_primality 144236559860544336156386115251 (2 : ZMod 144236559860544336156386115251)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 1), (131, 1), (2350891, 1), (170309499548514631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 1), (131, 1), (2350891, 1), (170309499548514631, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_5
      · exact prime_oneHundredTwentyTwoDP_11
      · exact prime_oneHundredTwentyTwoDP_131
      · exact prime_oneHundredTwentyTwoDP_2350891
      · exact prime_oneHundredTwentyTwoDP_170309499548514631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 144236559860544336156386115251) ^ 72118279930272168078193057625 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115251) ^ 28847311972108867231277223050 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115251) ^ 13112414532776757832398737750 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115251) ^ 1101042441683544550812107750 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115251) ^ 61353997212352395817750 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236559860544336156386115251) ^ 846908482750 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_144236559860544336156386115287 : Nat.Prime 144236559860544336156386115287 := by
  apply lucas_primality 144236559860544336156386115287 (5 : ZMod 144236559860544336156386115287)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (1534431487878131235706235269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (1534431487878131235706235269, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_47
      · exact prime_oneHundredTwentyTwoDP_1534431487878131235706235269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 144236559860544336156386115287) ^ 72118279930272168078193057643 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 144236559860544336156386115287) ^ 3068862975756262471412470538 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (5 : ZMod 144236559860544336156386115287) ^ 94 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyTwoDP_144236559860544336156386115289 : Nat.Prime 144236559860544336156386115289 := by
  apply lucas_primality 144236559860544336156386115289 (33 : ZMod 144236559860544336156386115289)
  · rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (181, 1), (1699, 1), (2791863109436682428689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (181, 1), (1699, 1), (2791863109436682428689, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyTwoDP_2
      · exact prime_oneHundredTwentyTwoDP_3
      · exact prime_oneHundredTwentyTwoDP_7
      · exact prime_oneHundredTwentyTwoDP_181
      · exact prime_oneHundredTwentyTwoDP_1699
      · exact prime_oneHundredTwentyTwoDP_2791863109436682428689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 144236559860544336156386115289) ^ 72118279930272168078193057644 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (33 : ZMod 144236559860544336156386115289) ^ 48078853286848112052128705096 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (33 : ZMod 144236559860544336156386115289) ^ 20605222837220619450912302184 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (33 : ZMod 144236559860544336156386115289) ^ 796887071052731138985558648 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (33 : ZMod 144236559860544336156386115289) ^ 84894973431750639291575112 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide
    · change (33 : ZMod 144236559860544336156386115289) ^ 51663192 ≠ 1
      rw [← oneHundredTwentyTwoDPFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115200 : Nat.totient 144236559860544336156386115200 = 56748479260082249026990080000 := by
  rw [← show ((([(2, 7), (5, 2), (61, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_61, prime_oneHundredTwentyTwoDP_171401, prime_oneHundredTwentyTwoDP_714027719, prime_oneHundredTwentyTwoDP_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115201 : Nat.totient 144236559860544336156386115201 = 96130083767332851423897629328 := by
  rw [← show ((([(3, 3), (3727, 1), (52747, 1), (27174054035038058327, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_3727, prime_oneHundredTwentyTwoDP_52747, prime_oneHundredTwentyTwoDP_27174054035038058327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115202 : Nat.totient 144236559860544336156386115202 = 67947373253689741966459092480 := by
  rw [← show ((([(2, 1), (23, 1), (97, 1), (211, 1), (112199, 1), (1365445429804229339, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_23, prime_oneHundredTwentyTwoDP_97, prime_oneHundredTwentyTwoDP_211, prime_oneHundredTwentyTwoDP_112199, prime_oneHundredTwentyTwoDP_1365445429804229339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115203 : Nat.totient 144236559860544336156386115203 = 144236559860544336156386115202 := by
  rw [← show ((([(144236559860544336156386115203, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_144236559860544336156386115203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115204 : Nat.totient 144236559860544336156386115204 = 39731138643843999476751255552 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (29, 1), (683, 1), (105200659, 1), (824060139854737, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_29, prime_oneHundredTwentyTwoDP_683, prime_oneHundredTwentyTwoDP_105200659, prime_oneHundredTwentyTwoDP_824060139854737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115205 : Nat.totient 144236559860544336156386115205 = 111667014085582711863008605200 := by
  rw [← show ((([(5, 1), (31, 1), (930558450713189265525071711, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_31, prime_oneHundredTwentyTwoDP_930558450713189265525071711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115206 : Nat.totient 144236559860544336156386115206 = 61064886210777423642882170880 := by
  rw [← show ((([(2, 1), (11, 1), (17, 1), (113, 1), (647, 1), (1023310333, 1), (5154821957563, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_17, prime_oneHundredTwentyTwoDP_113, prime_oneHundredTwentyTwoDP_647, prime_oneHundredTwentyTwoDP_1023310333, prime_oneHundredTwentyTwoDP_5154821957563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115207 : Nat.totient 144236559860544336156386115207 = 82337136362964877936408289280 := by
  rw [← show ((([(3, 1), (13, 1), (19, 1), (67, 1), (167, 1), (73867, 1), (70146781, 1), (3357435409, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_13, prime_oneHundredTwentyTwoDP_19, prime_oneHundredTwentyTwoDP_67, prime_oneHundredTwentyTwoDP_167, prime_oneHundredTwentyTwoDP_73867, prime_oneHundredTwentyTwoDP_70146781, prime_oneHundredTwentyTwoDP_3357435409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115208 : Nat.totient 144236559860544336156386115208 = 72037713213313890432934182912 := by
  rw [← show ((([(2, 3), (1009, 1), (8039, 1), (697033, 1), (2755793, 1), (1157156879, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_1009, prime_oneHundredTwentyTwoDP_8039, prime_oneHundredTwentyTwoDP_697033, prime_oneHundredTwentyTwoDP_2755793, prime_oneHundredTwentyTwoDP_1157156879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115209 : Nat.totient 144236559860544336156386115209 = 143606705887354186216838577360 := by
  rw [← show ((([(229, 1), (629853973190149939547537621, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_229, prime_oneHundredTwentyTwoDP_629853973190149939547537621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115210 : Nat.totient 144236559860544336156386115210 = 38463014412808371365503864704 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (563837, 1), (2842361254928174398637, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_563837, prime_oneHundredTwentyTwoDP_2842361254928174398637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115211 : Nat.totient 144236559860544336156386115211 = 123631277585952459830491700352 := by
  rw [← show ((([(7, 2), (2080027, 1), (1415175506116068922657, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_2080027, prime_oneHundredTwentyTwoDP_1415175506116068922657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115212 : Nat.totient 144236559860544336156386115212 = 72118230854226347520220495680 := by
  rw [← show ((([(2, 2), (1469521, 1), (24538022910278984811443, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_1469521, prime_oneHundredTwentyTwoDP_24538022910278984811443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115213 : Nat.totient 144236559860544336156386115213 = 94940516005659779424332815296 := by
  rw [← show ((([(3, 1), (79, 1), (22269943, 1), (662034467, 1), (41278822829, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_79, prime_oneHundredTwentyTwoDP_22269943, prime_oneHundredTwentyTwoDP_662034467, prime_oneHundredTwentyTwoDP_41278822829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115214 : Nat.totient 144236559860544336156386115214 = 71774834112280476748120871520 := by
  rw [← show ((([(2, 1), (283, 1), (811, 1), (427664667707, 1), (734741716477, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_283, prime_oneHundredTwentyTwoDP_811, prime_oneHundredTwentyTwoDP_427664667707, prime_oneHundredTwentyTwoDP_734741716477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115215 : Nat.totient 144236559860544336156386115215 = 115239196838145934612374528000 := by
  rw [← show ((([(5, 1), (769, 1), (9057356501, 1), (4141689618534647, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_769, prime_oneHundredTwentyTwoDP_9057356501, prime_oneHundredTwentyTwoDP_4141689618534647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115216 : Nat.totient 144236559860544336156386115216 = 45152498012163294371677470720 := by
  rw [← show ((([(2, 4), (3, 1), (37, 1), (41, 1), (109, 1), (673, 1), (1164659, 1), (1467043, 1), (15803939, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_37, prime_oneHundredTwentyTwoDP_41, prime_oneHundredTwentyTwoDP_109, prime_oneHundredTwentyTwoDP_673, prime_oneHundredTwentyTwoDP_1164659, prime_oneHundredTwentyTwoDP_1467043, prime_oneHundredTwentyTwoDP_15803939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115217 : Nat.totient 144236559860544336156386115217 = 131122886772730135542460422400 := by
  rw [← show ((([(11, 1), (108503, 1), (2618741, 1), (46147521047443889, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_108503, prime_oneHundredTwentyTwoDP_2618741, prime_oneHundredTwentyTwoDP_46147521047443889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115218 : Nat.totient 144236559860544336156386115218 = 61804654149220292586899310912 := by
  rw [← show ((([(2, 1), (7, 1), (5647, 1), (925943, 1), (63459523, 1), (31049061389, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_5647, prime_oneHundredTwentyTwoDP_925943, prime_oneHundredTwentyTwoDP_63459523, prime_oneHundredTwentyTwoDP_31049061389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115219 : Nat.totient 144236559860544336156386115219 = 96157706573597122606767739632 := by
  rw [← show ((([(3, 2), (970352199613, 1), (16515945896078807, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_970352199613, prime_oneHundredTwentyTwoDP_16515945896078807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115220 : Nat.totient 144236559860544336156386115220 = 53170572075247063004453867520 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (1031, 1), (1549, 1), (76480009, 1), (4541967206407, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_13, prime_oneHundredTwentyTwoDP_1031, prime_oneHundredTwentyTwoDP_1549, prime_oneHundredTwentyTwoDP_76480009, prime_oneHundredTwentyTwoDP_4541967206407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115221 : Nat.totient 144236559860544336156386115221 = 144236559860544336156386115220 := by
  rw [← show ((([(144236559860544336156386115221, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_144236559860544336156386115221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115222 : Nat.totient 144236559860544336156386115222 = 48078853286848112052128705072 := by
  rw [← show ((([(2, 1), (3, 1), (24039426643424056026064352537, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_24039426643424056026064352537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115223 : Nat.totient 144236559860544336156386115223 = 135752054808043335494030536704 := by
  rw [← show ((([(17, 1), (88651943, 1), (95705781893674799233, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_17, prime_oneHundredTwentyTwoDP_88651943, prime_oneHundredTwentyTwoDP_95705781893674799233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115224 : Nat.totient 144236559860544336156386115224 = 72117635228450026063692031840 := by
  rw [← show ((([(2, 3), (111863, 1), (161175455535503625144581, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_111863, prime_oneHundredTwentyTwoDP_161175455535503625144581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115225 : Nat.totient 144236559860544336156386115225 = 62991928871353715581634457600 := by
  rw [← show ((([(3, 1), (5, 2), (7, 1), (23, 1), (809, 1), (6130667, 1), (2408418571523641, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_23, prime_oneHundredTwentyTwoDP_809, prime_oneHundredTwentyTwoDP_6130667, prime_oneHundredTwentyTwoDP_2408418571523641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115226 : Nat.totient 144236559860544336156386115226 = 68299771116116635056180414720 := by
  rw [← show ((([(2, 1), (19, 1), (4523, 1), (9137, 1), (299087, 1), (307088822935171, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_19, prime_oneHundredTwentyTwoDP_4523, prime_oneHundredTwentyTwoDP_9137, prime_oneHundredTwentyTwoDP_299087, prime_oneHundredTwentyTwoDP_307088822935171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115227 : Nat.totient 144236559860544336156386115227 = 144220285849502866638597954936 := by
  rw [← show ((([(8863, 1), (16274011041469517788151429, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_8863, prime_oneHundredTwentyTwoDP_16274011041469517788151429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115228 : Nat.totient 144236559860544336156386115228 = 43707494678466467424037178880 := by
  rw [← show ((([(2, 2), (3, 4), (11, 1), (78929, 1), (512744558079028277813, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_78929, prime_oneHundredTwentyTwoDP_512744558079028277813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115229 : Nat.totient 144236559860544336156386115229 = 141420441762473159385701222400 := by
  rw [← show ((([(53, 1), (2207, 1), (7103, 1), (13337, 1), (4181509, 1), (3112892701, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_53, prime_oneHundredTwentyTwoDP_2207, prime_oneHundredTwentyTwoDP_7103, prime_oneHundredTwentyTwoDP_13337, prime_oneHundredTwentyTwoDP_4181509, prime_oneHundredTwentyTwoDP_3112892701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115230 : Nat.totient 144236559860544336156386115230 = 57694562247093488326253952000 := by
  rw [← show ((([(2, 1), (5, 1), (1275121, 1), (3507113, 1), (3225330312651451, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_1275121, prime_oneHundredTwentyTwoDP_3507113, prime_oneHundredTwentyTwoDP_3225330312651451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115231 : Nat.totient 144236559860544336156386115231 = 96157706573696224104257410152 := by
  rw [← show ((([(3, 1), (48078853286848112052128705077, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_48078853286848112052128705077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115232 : Nat.totient 144236559860544336156386115232 = 61070901420930707656212845568 := by
  rw [← show ((([(2, 5), (7, 1), (83, 1), (268935843269, 1), (28846993512509, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_83, prime_oneHundredTwentyTwoDP_268935843269, prime_oneHundredTwentyTwoDP_28846993512509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115233 : Nat.totient 144236559860544336156386115233 = 128550355733657858457120390720 := by
  rw [← show ((([(13, 1), (29, 1), (31188684391, 1), (12266960018617519, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_13, prime_oneHundredTwentyTwoDP_29, prime_oneHundredTwentyTwoDP_31188684391, prime_oneHundredTwentyTwoDP_12266960018617519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115234 : Nat.totient 144236559860544336156386115234 = 48075507274370775556057124480 := by
  rw [← show ((([(2, 1), (3, 1), (14369, 1), (1673006238668248035775931, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_14369, prime_oneHundredTwentyTwoDP_1673006238668248035775931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115235 : Nat.totient 144236559860544336156386115235 = 115386658536287187187405521408 := by
  rw [← show ((([(5, 1), (44563, 1), (100633456177, 1), (6432629569997, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_44563, prime_oneHundredTwentyTwoDP_100633456177, prime_oneHundredTwentyTwoDP_6432629569997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115236 : Nat.totient 144236559860544336156386115236 = 69789157777574012960050901760 := by
  rw [← show ((([(2, 2), (31, 1), (42589, 1), (64187, 1), (425509391271644473, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_31, prime_oneHundredTwentyTwoDP_42589, prime_oneHundredTwentyTwoDP_64187, prime_oneHundredTwentyTwoDP_425509391271644473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115237 : Nat.totient 144236559860544336156386115237 = 95921353977007472951531619840 := by
  rw [← show ((([(3, 2), (443, 1), (4973, 1), (34281646961, 1), (212201760467, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_443, prime_oneHundredTwentyTwoDP_4973, prime_oneHundredTwentyTwoDP_34281646961, prime_oneHundredTwentyTwoDP_212201760467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115238 : Nat.totient 144236559860544336156386115238 = 72118279823340472962667592256 := by
  rw [← show ((([(2, 1), (834881737, 1), (4239579373, 1), (20375000519, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_834881737, prime_oneHundredTwentyTwoDP_4239579373, prime_oneHundredTwentyTwoDP_20375000519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115239 : Nat.totient 144236559860544336156386115239 = 107442644563475066652411114720 := by
  rw [← show ((([(7, 1), (11, 1), (43, 1), (47, 1), (926868914453718656421767, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_43, prime_oneHundredTwentyTwoDP_47, prime_oneHundredTwentyTwoDP_926868914453718656421767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115240 : Nat.totient 144236559860544336156386115240 = 35848267371108314870584541184 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (17, 1), (103, 1), (43753, 1), (15689175712571554709, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_17, prime_oneHundredTwentyTwoDP_103, prime_oneHundredTwentyTwoDP_43753, prime_oneHundredTwentyTwoDP_15689175712571554709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115241 : Nat.totient 144236559860544336156386115241 = 142503911331345802170003456000 := by
  rw [← show ((([(101, 1), (617, 1), (2017, 1), (58889, 1), (19486271086154021, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_101, prime_oneHundredTwentyTwoDP_617, prime_oneHundredTwentyTwoDP_2017, prime_oneHundredTwentyTwoDP_58889, prime_oneHundredTwentyTwoDP_19486271086154021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115242 : Nat.totient 144236559860544336156386115242 = 70845841669404481867211592960 := by
  rw [← show ((([(2, 1), (71, 1), (277, 1), (9904457287, 1), (370234221282449, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_71, prime_oneHundredTwentyTwoDP_277, prime_oneHundredTwentyTwoDP_9904457287, prime_oneHundredTwentyTwoDP_370234221282449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115243 : Nat.totient 144236559860544336156386115243 = 96157706573676971270370524904 := by
  rw [← show ((([(3, 1), (4997064247327, 1), (9621419879195303, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_4997064247327, prime_oneHundredTwentyTwoDP_9621419879195303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115244 : Nat.totient 144236559860544336156386115244 = 72116828770646229446724696704 := by
  rw [← show ((([(2, 2), (49697, 1), (725579812969315734130763, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_49697, prime_oneHundredTwentyTwoDP_725579812969315734130763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115245 : Nat.totient 144236559860544336156386115245 = 109316124921731749568915094144 := by
  rw [← show ((([(5, 1), (19, 1), (23474587, 1), (64677584209656769033, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_19, prime_oneHundredTwentyTwoDP_23474587, prime_oneHundredTwentyTwoDP_64677584209656769033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115246 : Nat.totient 144236559860544336156386115246 = 37471488519547468983700905984 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (13, 1), (73, 1), (1019, 1), (3407, 1), (347449971587835313, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_13, prime_oneHundredTwentyTwoDP_73, prime_oneHundredTwentyTwoDP_1019, prime_oneHundredTwentyTwoDP_3407, prime_oneHundredTwentyTwoDP_347449971587835313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115247 : Nat.totient 144236559860544336156386115247 = 143637999835324290046357875840 := by
  rw [← show ((([(241, 1), (2109979, 1), (283648296797652807373, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_241, prime_oneHundredTwentyTwoDP_2109979, prime_oneHundredTwentyTwoDP_283648296797652807373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115248 : Nat.totient 144236559860544336156386115248 = 68854628083080634836447605760 := by
  rw [← show ((([(2, 4), (23, 1), (571, 1), (15259, 1), (25087, 1), (11339213, 1), (158137079, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_23, prime_oneHundredTwentyTwoDP_571, prime_oneHundredTwentyTwoDP_15259, prime_oneHundredTwentyTwoDP_25087, prime_oneHundredTwentyTwoDP_11339213, prime_oneHundredTwentyTwoDP_158137079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115249 : Nat.totient 144236559860544336156386115249 = 96109493974216181093367532800 := by
  rw [← show ((([(3, 1), (2579, 1), (11003, 1), (72661, 1), (110581, 1), (210867554899, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_2579, prime_oneHundredTwentyTwoDP_11003, prime_oneHundredTwentyTwoDP_72661, prime_oneHundredTwentyTwoDP_110581, prime_oneHundredTwentyTwoDP_210867554899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115250 : Nat.totient 144236559860544336156386115250 = 52049256921168982607691000000 := by
  rw [← show ((([(2, 1), (5, 3), (11, 1), (131, 1), (2350891, 1), (170309499548514631, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_131, prime_oneHundredTwentyTwoDP_2350891, prime_oneHundredTwentyTwoDP_170309499548514631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115251 : Nat.totient 144236559860544336156386115251 = 144236559860544336156386115250 := by
  rw [← show ((([(144236559860544336156386115251, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_144236559860544336156386115251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115252 : Nat.totient 144236559860544336156386115252 = 47151154882470799287922907904 := by
  rw [← show ((([(2, 2), (3, 1), (59, 1), (419, 1), (60593479, 1), (8024208162654569, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_59, prime_oneHundredTwentyTwoDP_419, prime_oneHundredTwentyTwoDP_60593479, prime_oneHundredTwentyTwoDP_8024208162654569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115253 : Nat.totient 144236559860544336156386115253 = 120289764270456178299988464384 := by
  rw [← show ((([(7, 1), (37, 1), (649799, 1), (818684509, 1), (1046839207637, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_37, prime_oneHundredTwentyTwoDP_649799, prime_oneHundredTwentyTwoDP_818684509, prime_oneHundredTwentyTwoDP_1046839207637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115254 : Nat.totient 144236559860544336156386115254 = 72118277230160258639347821480 := by
  rw [← show ((([(2, 1), (26709367, 1), (2700111909438818526781, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_26709367, prime_oneHundredTwentyTwoDP_2700111909438818526781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115255 : Nat.totient 144236559860544336156386115255 = 76925093520583141466561335296 := by
  rw [← show ((([(3, 3), (5, 1), (71777, 1), (14885255192191900547569, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_71777, prime_oneHundredTwentyTwoDP_14885255192191900547569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115256 : Nat.totient 144236559860544336156386115256 = 72099821194178167594204874496 := by
  rw [← show ((([(2, 3), (3907, 1), (142247822149, 1), (32441156753849, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3907, prime_oneHundredTwentyTwoDP_142247822149, prime_oneHundredTwentyTwoDP_32441156753849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115257 : Nat.totient 144236559860544336156386115257 = 131551543855123992101385861120 := by
  rw [← show ((([(17, 1), (41, 1), (149, 1), (211927, 1), (6553450429077335947, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_17, prime_oneHundredTwentyTwoDP_41, prime_oneHundredTwentyTwoDP_149, prime_oneHundredTwentyTwoDP_211927, prime_oneHundredTwentyTwoDP_6553450429077335947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115258 : Nat.totient 144236559860544336156386115258 = 48063985484358189388922880000 := by
  rw [← show ((([(2, 1), (3, 1), (3347, 1), (95561, 1), (688816129, 1), (109114985501, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_3347, prime_oneHundredTwentyTwoDP_95561, prime_oneHundredTwentyTwoDP_688816129, prime_oneHundredTwentyTwoDP_109114985501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115259 : Nat.totient 144236559860544336156386115259 = 132093082076979307017607429248 := by
  rw [← show ((([(13, 1), (127, 1), (6348421233053, 1), (13761397726253, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_13, prime_oneHundredTwentyTwoDP_127, prime_oneHundredTwentyTwoDP_6348421233053, prime_oneHundredTwentyTwoDP_13761397726253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115260 : Nat.totient 144236559860544336156386115260 = 49452534809329486682189524896 := by
  rw [← show ((([(2, 2), (5, 1), (7, 2), (147180163123004424649373587, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_147180163123004424649373587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115261 : Nat.totient 144236559860544336156386115261 = 85795306199477474195508480000 := by
  rw [← show ((([(3, 1), (11, 1), (61, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_61, prime_oneHundredTwentyTwoDP_461, prime_oneHundredTwentyTwoDP_69997, prime_oneHundredTwentyTwoDP_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115262 : Nat.totient 144236559860544336156386115262 = 69631442691297265730669159064 := by
  rw [← show ((([(2, 1), (29, 1), (2486837238974902347523898539, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_29, prime_oneHundredTwentyTwoDP_2486837238974902347523898539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115263 : Nat.totient 144236559860544336156386115263 = 143749759840572583093938526656 := by
  rw [← show ((([(367, 1), (1543, 1), (255977, 1), (995044309510876399, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_367, prime_oneHundredTwentyTwoDP_1543, prime_oneHundredTwentyTwoDP_255977, prime_oneHundredTwentyTwoDP_995044309510876399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115264 : Nat.totient 144236559860544336156386115264 = 45371156245299221858735357952 := by
  rw [← show ((([(2, 6), (3, 2), (19, 1), (257, 1), (51282140938425950632433, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_19, prime_oneHundredTwentyTwoDP_257, prime_oneHundredTwentyTwoDP_51282140938425950632433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115265 : Nat.totient 144236559860544336156386115265 = 115218607543302712686021657600 := by
  rw [← show ((([(5, 1), (677, 1), (581137, 1), (2021573651, 1), (36270086147, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_677, prime_oneHundredTwentyTwoDP_581137, prime_oneHundredTwentyTwoDP_2021573651, prime_oneHundredTwentyTwoDP_36270086147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115266 : Nat.totient 144236559860544336156386115266 = 72118279432798571744965559520 := by
  rw [← show ((([(2, 1), (148566191, 1), (6510166489, 1), (74564700167, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_148566191, prime_oneHundredTwentyTwoDP_6510166489, prime_oneHundredTwentyTwoDP_74564700167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115267 : Nat.totient 144236559860544336156386115267 = 79464060739415930604534144000 := by
  rw [← show ((([(3, 1), (7, 1), (31, 1), (281, 1), (5581, 1), (346217999, 1), (408062215003, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_31, prime_oneHundredTwentyTwoDP_281, prime_oneHundredTwentyTwoDP_5581, prime_oneHundredTwentyTwoDP_346217999, prime_oneHundredTwentyTwoDP_408062215003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115268 : Nat.totient 144236559860544336156386115268 = 72118279930197134921146651880 := by
  rw [← show ((([(2, 2), (961176771587, 1), (37515617346431291, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_961176771587, prime_oneHundredTwentyTwoDP_37515617346431291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115269 : Nat.totient 144236559860544336156386115269 = 144234291597796682563214962560 := by
  rw [← show ((([(63589, 1), (2268262747653593171089121, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_63589, prime_oneHundredTwentyTwoDP_2268262747653593171089121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115270 : Nat.totient 144236559860544336156386115270 = 38285125541530882934220800000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (401, 1), (761, 1), (1229, 1), (85991, 1), (149080276366271, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_401, prime_oneHundredTwentyTwoDP_761, prime_oneHundredTwentyTwoDP_1229, prime_oneHundredTwentyTwoDP_85991, prime_oneHundredTwentyTwoDP_149080276366271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115271 : Nat.totient 144236559860544336156386115271 = 137965401809138839570504657920 := by
  rw [← show ((([(23, 2), (42128641, 1), (6472055515108145239, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_23, prime_oneHundredTwentyTwoDP_42128641, prime_oneHundredTwentyTwoDP_6472055515108145239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115272 : Nat.totient 144236559860544336156386115272 = 60518836305123497687994173760 := by
  rw [← show ((([(2, 3), (11, 1), (13, 1), (126080908969007286849987863, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_13, prime_oneHundredTwentyTwoDP_126080908969007286849987863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115273 : Nat.totient 144236559860544336156386115273 = 95542529077112167389081600000 := by
  rw [← show ((([(3, 2), (251, 1), (433, 1), (9343, 1), (148201, 1), (9229177, 1), (11539069, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_251, prime_oneHundredTwentyTwoDP_433, prime_oneHundredTwentyTwoDP_9343, prime_oneHundredTwentyTwoDP_148201, prime_oneHundredTwentyTwoDP_9229177, prime_oneHundredTwentyTwoDP_11539069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115274 : Nat.totient 144236559860544336156386115274 = 57311102676308096945118569472 := by
  rw [← show ((([(2, 1), (7, 1), (17, 2), (67, 1), (532077230729241838839857, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_17, prime_oneHundredTwentyTwoDP_67, prime_oneHundredTwentyTwoDP_532077230729241838839857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115275 : Nat.totient 144236559860544336156386115275 = 115389247887712722176677176480 := by
  rw [← show ((([(5, 2), (159654481919, 1), (36137177767103869, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_159654481919, prime_oneHundredTwentyTwoDP_36137177767103869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115276 : Nat.totient 144236559860544336156386115276 = 48022882559669315844434034432 := by
  rw [← show ((([(2, 2), (3, 1), (859, 1), (30339944179, 1), (461196675788593, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_859, prime_oneHundredTwentyTwoDP_30339944179, prime_oneHundredTwentyTwoDP_461196675788593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115277 : Nat.totient 144236559860544336156386115277 = 144236556531447796342550538720 := by
  rw [← show ((([(43326037, 1), (3329096539813792250521, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_43326037, prime_oneHundredTwentyTwoDP_3329096539813792250521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115278 : Nat.totient 144236559860544336156386115278 = 72118279930272168078193057638 := by
  rw [← show ((([(2, 1), (72118279930272168078193057639, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_72118279930272168078193057639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115279 : Nat.totient 144236559860544336156386115279 = 96157706552112464457155580480 := by
  rw [← show ((([(3, 1), (4455095321, 1), (10791879819095819533, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_4455095321, prime_oneHundredTwentyTwoDP_10791879819095819533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115280 : Nat.totient 144236559860544336156386115280 = 57648431290633314388073496576 := by
  rw [← show ((([(2, 4), (5, 1), (1249, 1), (192987195757, 1), (7479876627437, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_1249, prime_oneHundredTwentyTwoDP_192987195757, prime_oneHundredTwentyTwoDP_7479876627437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115281 : Nat.totient 144236559860544336156386115281 = 123411726241631995459740756048 := by
  rw [← show ((([(7, 1), (563, 1), (7288399, 1), (5021538316451439859, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_563, prime_oneHundredTwentyTwoDP_7288399, prime_oneHundredTwentyTwoDP_5021538316451439859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115282 : Nat.totient 144236559860544336156386115282 = 45527136049426490098614374400 := by
  rw [← show ((([(2, 1), (3, 3), (43, 1), (53, 1), (89, 1), (1583, 1), (42131, 1), (197453384225641, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_43, prime_oneHundredTwentyTwoDP_53, prime_oneHundredTwentyTwoDP_89, prime_oneHundredTwentyTwoDP_1583, prime_oneHundredTwentyTwoDP_42131, prime_oneHundredTwentyTwoDP_197453384225641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115283 : Nat.totient 144236559860544336156386115283 = 124222874520880918819631778480 := by
  rw [← show ((([(11, 2), (19, 1), (773888373239, 1), (81069606011903, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_19, prime_oneHundredTwentyTwoDP_773888373239, prime_oneHundredTwentyTwoDP_81069606011903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115284 : Nat.totient 144236559860544336156386115284 = 72118279827407942930762613888 := by
  rw [← show ((([(2, 2), (701101669, 1), (51432112573014120209, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_701101669, prime_oneHundredTwentyTwoDP_51432112573014120209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115285 : Nat.totient 144236559860544336156386115285 = 70988388674263485588873621504 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (3623, 1), (91033, 1), (2242712249024784457, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_13, prime_oneHundredTwentyTwoDP_3623, prime_oneHundredTwentyTwoDP_91033, prime_oneHundredTwentyTwoDP_2242712249024784457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115286 : Nat.totient 144236559860544336156386115286 = 70583848442394036842486822328 := by
  rw [← show ((([(2, 1), (47, 1), (1534431487878131235706235269, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_47, prime_oneHundredTwentyTwoDP_1534431487878131235706235269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115287 : Nat.totient 144236559860544336156386115287 = 144236559860544336156386115286 := by
  rw [← show ((([(144236559860544336156386115287, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_144236559860544336156386115287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115288 : Nat.totient 144236559860544336156386115288 = 40958641956874925640201615360 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (181, 1), (1699, 1), (2791863109436682428689, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_181, prime_oneHundredTwentyTwoDP_1699, prime_oneHundredTwentyTwoDP_2791863109436682428689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115289 : Nat.totient 144236559860544336156386115289 = 144236559860544336156386115288 := by
  rw [← show ((([(144236559860544336156386115289, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_144236559860544336156386115289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115290 : Nat.totient 144236559860544336156386115290 = 56132435540113311566843953920 := by
  rw [← show ((([(2, 1), (5, 1), (37, 1), (20231, 1), (563999, 1), (34164726430140893, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_37, prime_oneHundredTwentyTwoDP_20231, prime_oneHundredTwentyTwoDP_563999, prime_oneHundredTwentyTwoDP_34164726430140893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115291 : Nat.totient 144236559860544336156386115291 = 87380633965549509936525925632 := by
  rw [← show ((([(3, 2), (17, 1), (29, 2), (1120954356085148680425467, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_17, prime_oneHundredTwentyTwoDP_29, prime_oneHundredTwentyTwoDP_1120954356085148680425467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115292 : Nat.totient 144236559860544336156386115292 = 71116048533103174933356870144 := by
  rw [← show ((([(2, 2), (79, 1), (797, 1), (8596111529, 1), (66623571467749, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_79, prime_oneHundredTwentyTwoDP_797, prime_oneHundredTwentyTwoDP_8596111529, prime_oneHundredTwentyTwoDP_66623571467749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115293 : Nat.totient 144236559860544336156386115293 = 142888554615357878777674090816 := by
  rw [← show ((([(107, 1), (11124129287, 1), (121178493845523377, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_107, prime_oneHundredTwentyTwoDP_11124129287, prime_oneHundredTwentyTwoDP_121178493845523377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115294 : Nat.totient 144236559860544336156386115294 = 41711608978098815747032166400 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (23, 1), (503, 1), (3217, 1), (14860841, 1), (3951310427063, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_11, prime_oneHundredTwentyTwoDP_23, prime_oneHundredTwentyTwoDP_503, prime_oneHundredTwentyTwoDP_3217, prime_oneHundredTwentyTwoDP_14860841, prime_oneHundredTwentyTwoDP_3951310427063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115295 : Nat.totient 144236559860544336156386115295 = 98639908572177780726924569088 := by
  rw [← show ((([(5, 1), (7, 1), (373, 1), (51196563037, 1), (215803096946837, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_373, prime_oneHundredTwentyTwoDP_51196563037, prime_oneHundredTwentyTwoDP_215803096946837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115296 : Nat.totient 144236559860544336156386115296 = 72027615606226786623581061120 := by
  rw [← show ((([(2, 5), (929, 1), (5527, 1), (877849768061400605441, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_929, prime_oneHundredTwentyTwoDP_5527, prime_oneHundredTwentyTwoDP_877849768061400605441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115297 : Nat.totient 144236559860544336156386115297 = 95567395184316304934464263312 := by
  rw [← show ((([(3, 1), (163, 1), (247067, 1), (1193855472820581666619, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_163, prime_oneHundredTwentyTwoDP_247067, prime_oneHundredTwentyTwoDP_1193855472820581666619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115298 : Nat.totient 144236559860544336156386115298 = 62851977909333608928522652800 := by
  rw [← show ((([(2, 1), (13, 1), (31, 1), (41, 1), (4364720688148167286702963, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_13, prime_oneHundredTwentyTwoDP_31, prime_oneHundredTwentyTwoDP_41, prime_oneHundredTwentyTwoDP_4364720688148167286702963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115299 : Nat.totient 144236559860544336156386115299 = 142032204988245999467836545024 := by
  rw [← show ((([(97, 1), (199, 1), (3126377, 1), (2390062169917025629, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_97, prime_oneHundredTwentyTwoDP_199, prime_oneHundredTwentyTwoDP_3126377, prime_oneHundredTwentyTwoDP_2390062169917025629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115300 : Nat.totient 144236559860544336156386115300 = 38340197381460986479908311040 := by
  rw [← show ((([(2, 2), (3, 2), (5, 2), (313, 1), (512021866739596507477409, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_5, prime_oneHundredTwentyTwoDP_313, prime_oneHundredTwentyTwoDP_512021866739596507477409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115301 : Nat.totient 144236559860544336156386115301 = 143481394625672376281221753800 := by
  rw [← show ((([(191, 2), (3953744685193507199813221, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_191, prime_oneHundredTwentyTwoDP_3953744685193507199813221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115302 : Nat.totient 144236559860544336156386115302 = 58151496762410346186983521920 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (269, 1), (347, 1), (2339, 1), (2483600521622429411, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115302 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_2, prime_oneHundredTwentyTwoDP_7, prime_oneHundredTwentyTwoDP_19, prime_oneHundredTwentyTwoDP_269, prime_oneHundredTwentyTwoDP_347, prime_oneHundredTwentyTwoDP_2339, prime_oneHundredTwentyTwoDP_2483600521622429411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyTwoDP_144236559860544336156386115303 : Nat.totient 144236559860544336156386115303 = 96149412105160600538487140544 := by
  rw [← show ((([(3, 1), (11593, 1), (16598238599, 1), (249859727374643, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236559860544336156386115303 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyTwoDP_3, prime_oneHundredTwentyTwoDP_11593, prime_oneHundredTwentyTwoDP_16598238599, prime_oneHundredTwentyTwoDP_249859727374643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentyTwoDP : certifiedKill 3 144236559860544336156386115199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115200, phi_oneHundredTwentyTwoDP_144236559860544336156386115201, phi_oneHundredTwentyTwoDP_144236559860544336156386115202,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115203, phi_oneHundredTwentyTwoDP_144236559860544336156386115204, phi_oneHundredTwentyTwoDP_144236559860544336156386115205,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115206, phi_oneHundredTwentyTwoDP_144236559860544336156386115207, phi_oneHundredTwentyTwoDP_144236559860544336156386115208,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115209, phi_oneHundredTwentyTwoDP_144236559860544336156386115210, phi_oneHundredTwentyTwoDP_144236559860544336156386115211,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115212, phi_oneHundredTwentyTwoDP_144236559860544336156386115213, phi_oneHundredTwentyTwoDP_144236559860544336156386115214,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115215, phi_oneHundredTwentyTwoDP_144236559860544336156386115216, phi_oneHundredTwentyTwoDP_144236559860544336156386115217,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115218, phi_oneHundredTwentyTwoDP_144236559860544336156386115219, phi_oneHundredTwentyTwoDP_144236559860544336156386115220,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115221, phi_oneHundredTwentyTwoDP_144236559860544336156386115222, phi_oneHundredTwentyTwoDP_144236559860544336156386115223,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115224, phi_oneHundredTwentyTwoDP_144236559860544336156386115225, phi_oneHundredTwentyTwoDP_144236559860544336156386115226,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115227, phi_oneHundredTwentyTwoDP_144236559860544336156386115228, phi_oneHundredTwentyTwoDP_144236559860544336156386115229,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115230, phi_oneHundredTwentyTwoDP_144236559860544336156386115231, phi_oneHundredTwentyTwoDP_144236559860544336156386115232,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115233, phi_oneHundredTwentyTwoDP_144236559860544336156386115234, phi_oneHundredTwentyTwoDP_144236559860544336156386115235,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115236, phi_oneHundredTwentyTwoDP_144236559860544336156386115237, phi_oneHundredTwentyTwoDP_144236559860544336156386115238,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115239, phi_oneHundredTwentyTwoDP_144236559860544336156386115240, phi_oneHundredTwentyTwoDP_144236559860544336156386115241,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115242, phi_oneHundredTwentyTwoDP_144236559860544336156386115243, phi_oneHundredTwentyTwoDP_144236559860544336156386115244,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115245, phi_oneHundredTwentyTwoDP_144236559860544336156386115246, phi_oneHundredTwentyTwoDP_144236559860544336156386115247,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115248, phi_oneHundredTwentyTwoDP_144236559860544336156386115249, phi_oneHundredTwentyTwoDP_144236559860544336156386115250,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115251, phi_oneHundredTwentyTwoDP_144236559860544336156386115252, phi_oneHundredTwentyTwoDP_144236559860544336156386115253,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115254, phi_oneHundredTwentyTwoDP_144236559860544336156386115255, phi_oneHundredTwentyTwoDP_144236559860544336156386115256,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115257, phi_oneHundredTwentyTwoDP_144236559860544336156386115258, phi_oneHundredTwentyTwoDP_144236559860544336156386115259,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115260, phi_oneHundredTwentyTwoDP_144236559860544336156386115261, phi_oneHundredTwentyTwoDP_144236559860544336156386115262,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115263, phi_oneHundredTwentyTwoDP_144236559860544336156386115264, phi_oneHundredTwentyTwoDP_144236559860544336156386115265,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115266, phi_oneHundredTwentyTwoDP_144236559860544336156386115267, phi_oneHundredTwentyTwoDP_144236559860544336156386115268,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115269, phi_oneHundredTwentyTwoDP_144236559860544336156386115270, phi_oneHundredTwentyTwoDP_144236559860544336156386115271,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115272, phi_oneHundredTwentyTwoDP_144236559860544336156386115273, phi_oneHundredTwentyTwoDP_144236559860544336156386115274,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115275, phi_oneHundredTwentyTwoDP_144236559860544336156386115276, phi_oneHundredTwentyTwoDP_144236559860544336156386115277,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115278, phi_oneHundredTwentyTwoDP_144236559860544336156386115279, phi_oneHundredTwentyTwoDP_144236559860544336156386115280,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115281, phi_oneHundredTwentyTwoDP_144236559860544336156386115282, phi_oneHundredTwentyTwoDP_144236559860544336156386115283,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115284, phi_oneHundredTwentyTwoDP_144236559860544336156386115285, phi_oneHundredTwentyTwoDP_144236559860544336156386115286,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115287, phi_oneHundredTwentyTwoDP_144236559860544336156386115288, phi_oneHundredTwentyTwoDP_144236559860544336156386115289,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115290, phi_oneHundredTwentyTwoDP_144236559860544336156386115291, phi_oneHundredTwentyTwoDP_144236559860544336156386115292,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115293, phi_oneHundredTwentyTwoDP_144236559860544336156386115294, phi_oneHundredTwentyTwoDP_144236559860544336156386115295,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115296, phi_oneHundredTwentyTwoDP_144236559860544336156386115297, phi_oneHundredTwentyTwoDP_144236559860544336156386115298,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115299, phi_oneHundredTwentyTwoDP_144236559860544336156386115300, phi_oneHundredTwentyTwoDP_144236559860544336156386115301,
    phi_oneHundredTwentyTwoDP_144236559860544336156386115302, phi_oneHundredTwentyTwoDP_144236559860544336156386115303]

end TotientTailPeriodKiller
end Erdos249257
