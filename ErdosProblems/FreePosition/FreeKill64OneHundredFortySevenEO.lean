import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFortySevenEOFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortySevenEOFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortySevenEOFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortySevenEOFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortySevenEOFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortySevenEOFastPow a n * oneHundredFortySevenEOFastPow a n * a else oneHundredFortySevenEOFastPow a n * oneHundredFortySevenEOFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortySevenEO_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_233 : Nat.Prime 233 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_251 : Nat.Prime 251 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_277 : Nat.Prime 277 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_281 : Nat.Prime 281 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_311 : Nat.Prime 311 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_313 : Nat.Prime 313 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_337 : Nat.Prime 337 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_353 : Nat.Prime 353 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_359 : Nat.Prime 359 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_373 : Nat.Prime 373 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_401 : Nat.Prime 401 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_421 : Nat.Prime 421 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_431 : Nat.Prime 431 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_433 : Nat.Prime 433 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_439 : Nat.Prime 439 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_443 : Nat.Prime 443 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_449 : Nat.Prime 449 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_487 : Nat.Prime 487 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_491 : Nat.Prime 491 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_499 : Nat.Prime 499 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_503 : Nat.Prime 503 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_521 : Nat.Prime 521 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_523 : Nat.Prime 523 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_541 : Nat.Prime 541 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_547 : Nat.Prime 547 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_587 : Nat.Prime 587 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_593 : Nat.Prime 593 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_599 : Nat.Prime 599 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_601 : Nat.Prime 601 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_607 : Nat.Prime 607 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_613 : Nat.Prime 613 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_617 : Nat.Prime 617 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_641 : Nat.Prime 641 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_643 : Nat.Prime 643 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_653 : Nat.Prime 653 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_673 : Nat.Prime 673 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_683 : Nat.Prime 683 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_701 : Nat.Prime 701 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_719 : Nat.Prime 719 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_751 : Nat.Prime 751 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_757 : Nat.Prime 757 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_769 : Nat.Prime 769 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_857 : Nat.Prime 857 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_863 : Nat.Prime 863 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_877 : Nat.Prime 877 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_911 : Nat.Prime 911 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_937 : Nat.Prime 937 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1021 : Nat.Prime 1021 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1031 : Nat.Prime 1031 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1061 : Nat.Prime 1061 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1069 : Nat.Prime 1069 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1087 : Nat.Prime 1087 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1091 : Nat.Prime 1091 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1093 : Nat.Prime 1093 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1109 : Nat.Prime 1109 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1217 : Nat.Prime 1217 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1231 : Nat.Prime 1231 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1259 : Nat.Prime 1259 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1307 : Nat.Prime 1307 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1321 : Nat.Prime 1321 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1381 : Nat.Prime 1381 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1399 : Nat.Prime 1399 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1471 : Nat.Prime 1471 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1483 : Nat.Prime 1483 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1531 : Nat.Prime 1531 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1549 : Nat.Prime 1549 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1559 : Nat.Prime 1559 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1567 : Nat.Prime 1567 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1571 : Nat.Prime 1571 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1609 : Nat.Prime 1609 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1663 : Nat.Prime 1663 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1669 : Nat.Prime 1669 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1709 : Nat.Prime 1709 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1777 : Nat.Prime 1777 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1787 : Nat.Prime 1787 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1831 : Nat.Prime 1831 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1847 : Nat.Prime 1847 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1871 : Nat.Prime 1871 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1879 : Nat.Prime 1879 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1907 : Nat.Prime 1907 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1951 : Nat.Prime 1951 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1979 : Nat.Prime 1979 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1993 : Nat.Prime 1993 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2017 : Nat.Prime 2017 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2053 : Nat.Prime 2053 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2113 : Nat.Prime 2113 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2129 : Nat.Prime 2129 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2269 : Nat.Prime 2269 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2371 : Nat.Prime 2371 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2393 : Nat.Prime 2393 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2467 : Nat.Prime 2467 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2473 : Nat.Prime 2473 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2579 : Nat.Prime 2579 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2617 : Nat.Prime 2617 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2621 : Nat.Prime 2621 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2633 : Nat.Prime 2633 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2657 : Nat.Prime 2657 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2693 : Nat.Prime 2693 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2731 : Nat.Prime 2731 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2909 : Nat.Prime 2909 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3001 : Nat.Prime 3001 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3041 : Nat.Prime 3041 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3203 : Nat.Prime 3203 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3259 : Nat.Prime 3259 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3361 : Nat.Prime 3361 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3559 : Nat.Prime 3559 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3613 : Nat.Prime 3613 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3617 : Nat.Prime 3617 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3643 : Nat.Prime 3643 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3659 : Nat.Prime 3659 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3671 : Nat.Prime 3671 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3793 : Nat.Prime 3793 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3821 : Nat.Prime 3821 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3931 : Nat.Prime 3931 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4001 : Nat.Prime 4001 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4243 : Nat.Prime 4243 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4283 : Nat.Prime 4283 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4441 : Nat.Prime 4441 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4447 : Nat.Prime 4447 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4513 : Nat.Prime 4513 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4733 : Nat.Prime 4733 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4759 : Nat.Prime 4759 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4871 : Nat.Prime 4871 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_5087 : Nat.Prime 5087 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_5227 : Nat.Prime 5227 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_5231 : Nat.Prime 5231 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_5443 : Nat.Prime 5443 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_5651 : Nat.Prime 5651 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_5987 : Nat.Prime 5987 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_6151 : Nat.Prime 6151 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_6277 : Nat.Prime 6277 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_6451 : Nat.Prime 6451 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7019 : Nat.Prime 7019 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7079 : Nat.Prime 7079 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7151 : Nat.Prime 7151 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7333 : Nat.Prime 7333 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7411 : Nat.Prime 7411 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7559 : Nat.Prime 7559 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7691 : Nat.Prime 7691 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_7867 : Nat.Prime 7867 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_8741 : Nat.Prime 8741 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_9733 : Nat.Prime 9733 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_9769 : Nat.Prime 9769 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_9883 : Nat.Prime 9883 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_10103 : Nat.Prime 10103 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_10273 : Nat.Prime 10273 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_10501 : Nat.Prime 10501 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_10889 : Nat.Prime 10889 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_12343 : Nat.Prime 12343 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_12541 : Nat.Prime 12541 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_12689 : Nat.Prime 12689 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_12823 : Nat.Prime 12823 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_13499 : Nat.Prime 13499 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_13591 : Nat.Prime 13591 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_13633 : Nat.Prime 13633 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_13781 : Nat.Prime 13781 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_14323 : Nat.Prime 14323 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_14411 : Nat.Prime 14411 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_14533 : Nat.Prime 14533 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_14737 : Nat.Prime 14737 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_15767 : Nat.Prime 15767 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_16097 : Nat.Prime 16097 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_16267 : Nat.Prime 16267 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_16603 : Nat.Prime 16603 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_16729 : Nat.Prime 16729 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_17207 : Nat.Prime 17207 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_17509 : Nat.Prime 17509 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_17599 : Nat.Prime 17599 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_18539 : Nat.Prime 18539 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_19141 : Nat.Prime 19141 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_21013 : Nat.Prime 21013 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_21911 : Nat.Prime 21911 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_22147 : Nat.Prime 22147 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_22699 : Nat.Prime 22699 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_23251 : Nat.Prime 23251 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_23327 : Nat.Prime 23327 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_23957 : Nat.Prime 23957 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_24029 : Nat.Prime 24029 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_24181 : Nat.Prime 24181 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_24337 : Nat.Prime 24337 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_26701 : Nat.Prime 26701 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_26759 : Nat.Prime 26759 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_29387 : Nat.Prime 29387 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_30223 : Nat.Prime 30223 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_30677 : Nat.Prime 30677 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_34159 : Nat.Prime 34159 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_34673 : Nat.Prime 34673 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_34963 : Nat.Prime 34963 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_38561 : Nat.Prime 38561 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_38707 : Nat.Prime 38707 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_38737 : Nat.Prime 38737 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_39079 : Nat.Prime 39079 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_39671 : Nat.Prime 39671 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_42703 : Nat.Prime 42703 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_44797 : Nat.Prime 44797 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_45361 : Nat.Prime 45361 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_46337 : Nat.Prime 46337 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_46381 : Nat.Prime 46381 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_47713 : Nat.Prime 47713 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_50051 : Nat.Prime 50051 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_50969 : Nat.Prime 50969 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_52783 : Nat.Prime 52783 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_56807 : Nat.Prime 56807 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_57283 : Nat.Prime 57283 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_58109 : Nat.Prime 58109 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_58699 : Nat.Prime 58699 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_64223 : Nat.Prime 64223 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_65033 : Nat.Prime 65033 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_66029 : Nat.Prime 66029 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_69877 : Nat.Prime 69877 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_71429 : Nat.Prime 71429 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_73571 : Nat.Prime 73571 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_76163 : Nat.Prime 76163 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_79229 : Nat.Prime 79229 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_80039 : Nat.Prime 80039 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_80233 : Nat.Prime 80233 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_80603 : Nat.Prime 80603 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_82561 : Nat.Prime 82561 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_86491 : Nat.Prime 86491 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_87811 : Nat.Prime 87811 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_88747 : Nat.Prime 88747 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_91183 : Nat.Prime 91183 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_95989 : Nat.Prime 95989 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_97453 : Nat.Prime 97453 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_97649 : Nat.Prime 97649 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_102911 : Nat.Prime 102911 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_103981 : Nat.Prime 103981 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_104917 : Nat.Prime 104917 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_106417 : Nat.Prime 106417 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_108793 : Nat.Prime 108793 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_110623 : Nat.Prime 110623 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_113357 : Nat.Prime 113357 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_115657 : Nat.Prime 115657 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_126173 : Nat.Prime 126173 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_136471 : Nat.Prime 136471 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_145829 : Nat.Prime 145829 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_185401 : Nat.Prime 185401 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_194819 : Nat.Prime 194819 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_200789 : Nat.Prime 200789 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_204917 : Nat.Prime 204917 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_207661 : Nat.Prime 207661 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_223637 : Nat.Prime 223637 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_226409 : Nat.Prime 226409 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_232801 : Nat.Prime 232801 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_234317 : Nat.Prime 234317 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_244873 : Nat.Prime 244873 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_257099 : Nat.Prime 257099 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_265037 : Nat.Prime 265037 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_271163 : Nat.Prime 271163 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_281683 : Nat.Prime 281683 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_281933 : Nat.Prime 281933 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_285007 : Nat.Prime 285007 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_289103 : Nat.Prime 289103 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_338231 : Nat.Prime 338231 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_341461 : Nat.Prime 341461 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_356399 : Nat.Prime 356399 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_384941 : Nat.Prime 384941 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_426757 : Nat.Prime 426757 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_436231 : Nat.Prime 436231 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_438281 : Nat.Prime 438281 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_467333 : Nat.Prime 467333 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_469069 : Nat.Prime 469069 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_476089 : Nat.Prime 476089 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_482101 : Nat.Prime 482101 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_514793 : Nat.Prime 514793 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_519119 : Nat.Prime 519119 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_523571 : Nat.Prime 523571 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_526283 : Nat.Prime 526283 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_543901 : Nat.Prime 543901 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_561367 : Nat.Prime 561367 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_570881 : Nat.Prime 570881 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_579259 : Nat.Prime 579259 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_600751 : Nat.Prime 600751 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_617359 : Nat.Prime 617359 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_631859 : Nat.Prime 631859 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_649573 : Nat.Prime 649573 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_677011 : Nat.Prime 677011 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_719731 : Nat.Prime 719731 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_761437 : Nat.Prime 761437 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_783613 : Nat.Prime 783613 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_787667 : Nat.Prime 787667 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_826571 : Nat.Prime 826571 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_869299 : Nat.Prime 869299 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_877619 : Nat.Prime 877619 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_931241 : Nat.Prime 931241 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_995713 : Nat.Prime 995713 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1053971 : Nat.Prime 1053971 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1201841 : Nat.Prime 1201841 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1256729 : Nat.Prime 1256729 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1354819 : Nat.Prime 1354819 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1438973 : Nat.Prime 1438973 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1512569 : Nat.Prime 1512569 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1625759 : Nat.Prime 1625759 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1648349 : Nat.Prime 1648349 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1654193 : Nat.Prime 1654193 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1672423 : Nat.Prime 1672423 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1734143 : Nat.Prime 1734143 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1747367 : Nat.Prime 1747367 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1752013 : Nat.Prime 1752013 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1755773 : Nat.Prime 1755773 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_1966597 : Nat.Prime 1966597 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2042753 : Nat.Prime 2042753 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2053021 : Nat.Prime 2053021 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2126617 : Nat.Prime 2126617 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2145629 : Nat.Prime 2145629 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2489909 : Nat.Prime 2489909 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2782279 : Nat.Prime 2782279 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2826181 : Nat.Prime 2826181 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2927087 : Nat.Prime 2927087 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_2985253 : Nat.Prime 2985253 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3368543 : Nat.Prime 3368543 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3429619 : Nat.Prime 3429619 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3451517 : Nat.Prime 3451517 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3507367 : Nat.Prime 3507367 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3549947 : Nat.Prime 3549947 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3586001 : Nat.Prime 3586001 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_3935629 : Nat.Prime 3935629 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4041299 : Nat.Prime 4041299 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4102229 : Nat.Prime 4102229 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4282273 : Nat.Prime 4282273 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4324433 : Nat.Prime 4324433 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_4344827 : Nat.Prime 4344827 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_6314617 : Nat.Prime 6314617 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_8401381 : Nat.Prime 8401381 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_8465627 : Nat.Prime 8465627 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_9294367 : Nat.Prime 9294367 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_9449183 : Nat.Prime 9449183 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_10896877 : Nat.Prime 10896877 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_10920757 : Nat.Prime 10920757 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_11996167 : Nat.Prime 11996167 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_12365383 : Nat.Prime 12365383 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_12993041 : Nat.Prime 12993041 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_13888577 : Nat.Prime 13888577 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_13907743 : Nat.Prime 13907743 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_13963909 : Nat.Prime 13963909 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_15079171 : Nat.Prime 15079171 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_15164213 : Nat.Prime 15164213 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_15874693 : Nat.Prime 15874693 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_16727479 : Nat.Prime 16727479 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_17875829 : Nat.Prime 17875829 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_18262633 : Nat.Prime 18262633 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_18709633 : Nat.Prime 18709633 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_18875191 : Nat.Prime 18875191 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_19066031 : Nat.Prime 19066031 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_19200301 : Nat.Prime 19200301 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_19725451 : Nat.Prime 19725451 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_19899881 : Nat.Prime 19899881 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_20216341 : Nat.Prime 20216341 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_20816759 : Nat.Prime 20816759 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_21720649 : Nat.Prime 21720649 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_23600209 : Nat.Prime 23600209 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_23641649 : Nat.Prime 23641649 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_24318629 : Nat.Prime 24318629 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_25513987 : Nat.Prime 25513987 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_25863419 : Nat.Prime 25863419 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_26120771 : Nat.Prime 26120771 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_26689963 : Nat.Prime 26689963 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_27732071 : Nat.Prime 27732071 := by
  norm_num

private theorem prime_oneHundredFortySevenEO_30412469 : Nat.Prime 30412469 := by
  apply lucas_primality 30412469 (2 : ZMod 30412469)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (347, 1), (21911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (347, 1), (21911, 1)] : List FactorBlock).map factorBlockValue).prod) = 30412469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_347
      · exact prime_oneHundredFortySevenEO_21911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30412469) ^ 15206234 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30412469) ^ 87644 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30412469) ^ 1388 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_31969337 : Nat.Prime 31969337 := by
  apply lucas_primality 31969337 (3 : ZMod 31969337)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (570881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (570881, 1)] : List FactorBlock).map factorBlockValue).prod) = 31969337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_570881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31969337) ^ 15984668 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31969337) ^ 4567048 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31969337) ^ 56 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_32517839 : Nat.Prime 32517839 := by
  apply lucas_primality 32517839 (7 : ZMod 32517839)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (41, 1), (23327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (41, 1), (23327, 1)] : List FactorBlock).map factorBlockValue).prod) = 32517839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_41
      · exact prime_oneHundredFortySevenEO_23327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 32517839) ^ 16258919 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 32517839) ^ 1912814 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 32517839) ^ 793118 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 32517839) ^ 1394 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_73
      · exact prime_oneHundredFortySevenEO_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_33229433 : Nat.Prime 33229433 := by
  apply lucas_primality 33229433 (3 : ZMod 33229433)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1951, 1), (2129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1951, 1), (2129, 1)] : List FactorBlock).map factorBlockValue).prod) = 33229433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_1951
      · exact prime_oneHundredFortySevenEO_2129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33229433) ^ 16614716 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33229433) ^ 17032 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33229433) ^ 15608 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_43942513 : Nat.Prime 43942513 := by
  apply lucas_primality 43942513 (10 : ZMod 43942513)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (53, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (53, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) = 43942513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_53
      · exact prime_oneHundredFortySevenEO_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 43942513) ^ 21971256 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43942513) ^ 14647504 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43942513) ^ 1910544 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43942513) ^ 829104 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 43942513) ^ 58512 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_45334501 : Nat.Prime 45334501 := by
  apply lucas_primality 45334501 (6 : ZMod 45334501)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (30223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (30223, 1)] : List FactorBlock).map factorBlockValue).prod) = 45334501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_30223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 45334501) ^ 22667250 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 45334501) ^ 15111500 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 45334501) ^ 9066900 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 45334501) ^ 1500 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_46802489 : Nat.Prime 46802489 := by
  apply lucas_primality 46802489 (3 : ZMod 46802489)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (42703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (42703, 1)] : List FactorBlock).map factorBlockValue).prod) = 46802489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_137
      · exact prime_oneHundredFortySevenEO_42703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 46802489) ^ 23401244 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 46802489) ^ 341624 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 46802489) ^ 1096 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_50793763 : Nat.Prime 50793763 := by
  apply lucas_primality 50793763 (11 : ZMod 50793763)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8465627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8465627, 1)] : List FactorBlock).map factorBlockValue).prod) = 50793763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_8465627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 50793763) ^ 25396881 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 50793763) ^ 16931254 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 50793763) ^ 6 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_55766203 : Nat.Prime 55766203 := by
  apply lucas_primality 55766203 (2 : ZMod 55766203)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9294367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9294367, 1)] : List FactorBlock).map factorBlockValue).prod) = 55766203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_9294367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55766203) ^ 27883101 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 55766203) ^ 18588734 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 55766203) ^ 6 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_57010907 : Nat.Prime 57010907 := by
  apply lucas_primality 57010907 (2 : ZMod 57010907)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (47, 1), (137, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (47, 1), (137, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 57010907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_47
      · exact prime_oneHundredFortySevenEO_137
      · exact prime_oneHundredFortySevenEO_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57010907) ^ 28505453 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 57010907) ^ 3000574 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 57010907) ^ 1212998 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 57010907) ^ 416138 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 57010907) ^ 244682 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_64957301 : Nat.Prime 64957301 := by
  apply lucas_primality 64957301 (2 : ZMod 64957301)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (649573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (649573, 1)] : List FactorBlock).map factorBlockValue).prod) = 64957301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_649573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 64957301) ^ 32478650 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64957301) ^ 12991460 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64957301) ^ 100 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_65322379 : Nat.Prime 65322379 := by
  apply lucas_primality 65322379 (2 : ZMod 65322379)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (173, 1), (1907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (173, 1), (1907, 1)] : List FactorBlock).map factorBlockValue).prod) = 65322379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_173
      · exact prime_oneHundredFortySevenEO_1907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65322379) ^ 32661189 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 65322379) ^ 21774126 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 65322379) ^ 5938398 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 65322379) ^ 377586 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 65322379) ^ 34254 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_66909917 : Nat.Prime 66909917 := by
  apply lucas_primality 66909917 (2 : ZMod 66909917)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16727479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16727479, 1)] : List FactorBlock).map factorBlockValue).prod) = 66909917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_16727479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66909917) ^ 33454958 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 66909917) ^ 4 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_71504707 : Nat.Prime 71504707 := by
  apply lucas_primality 71504707 (2 : ZMod 71504707)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (173, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (173, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) = 71504707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_173
      · exact prime_oneHundredFortySevenEO_757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71504707) ^ 35752353 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71504707) ^ 23834902 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71504707) ^ 10214958 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71504707) ^ 5500362 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71504707) ^ 413322 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71504707) ^ 94458 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_74192299 : Nat.Prime 74192299 := by
  apply lucas_primality 74192299 (3 : ZMod 74192299)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12365383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12365383, 1)] : List FactorBlock).map factorBlockValue).prod) = 74192299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_12365383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 74192299) ^ 37096149 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 74192299) ^ 24730766 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 74192299) ^ 6 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_76141909 : Nat.Prime 76141909 := by
  apply lucas_primality 76141909 (2 : ZMod 76141909)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (61, 1), (34673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (61, 1), (34673, 1)] : List FactorBlock).map factorBlockValue).prod) = 76141909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_34673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 76141909) ^ 38070954 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76141909) ^ 25380636 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76141909) ^ 1248228 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76141909) ^ 2196 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_84978809 : Nat.Prime 84978809 := by
  apply lucas_primality 84978809 (3 : ZMod 84978809)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (653, 1), (16267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (653, 1), (16267, 1)] : List FactorBlock).map factorBlockValue).prod) = 84978809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_653
      · exact prime_oneHundredFortySevenEO_16267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 84978809) ^ 42489404 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 84978809) ^ 130136 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 84978809) ^ 5224 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_90463463 : Nat.Prime 90463463 := by
  apply lucas_primality 90463463 (5 : ZMod 90463463)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1966597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1966597, 1)] : List FactorBlock).map factorBlockValue).prod) = 90463463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_1966597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 90463463) ^ 45231731 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 90463463) ^ 3933194 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 90463463) ^ 46 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_91596523 : Nat.Prime 91596523 := by
  apply lucas_primality 91596523 (5 : ZMod 91596523)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3001, 1), (5087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3001, 1), (5087, 1)] : List FactorBlock).map factorBlockValue).prod) = 91596523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_3001
      · exact prime_oneHundredFortySevenEO_5087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 91596523) ^ 45798261 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 91596523) ^ 30532174 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 91596523) ^ 30522 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 91596523) ^ 18006 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_93550973 : Nat.Prime 93550973 := by
  apply lucas_primality 93550973 (2 : ZMod 93550973)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (543901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (543901, 1)] : List FactorBlock).map factorBlockValue).prod) = 93550973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_43
      · exact prime_oneHundredFortySevenEO_543901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93550973) ^ 46775486 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93550973) ^ 2175604 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 93550973) ^ 172 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_93792679 : Nat.Prime 93792679 := by
  apply lucas_primality 93792679 (3 : ZMod 93792679)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (613, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (613, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) = 93792679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_613
      · exact prime_oneHundredFortySevenEO_3643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93792679) ^ 46896339 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 93792679) ^ 31264226 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 93792679) ^ 13398954 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 93792679) ^ 153006 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 93792679) ^ 25746 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_94400837 : Nat.Prime 94400837 := by
  apply lucas_primality 94400837 (2 : ZMod 94400837)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23600209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23600209, 1)] : List FactorBlock).map factorBlockValue).prod) = 94400837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_23600209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 94400837) ^ 47200418 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 94400837) ^ 4 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_99231071 : Nat.Prime 99231071 := by
  apply lucas_primality 99231071 (7 : ZMod 99231071)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (173, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (173, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 99231071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_41
      · exact prime_oneHundredFortySevenEO_173
      · exact prime_oneHundredFortySevenEO_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 99231071) ^ 49615535 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 99231071) ^ 19846214 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 99231071) ^ 2420270 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 99231071) ^ 573590 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 99231071) ^ 70930 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_107933869 : Nat.Prime 107933869 := by
  apply lucas_primality 107933869 (2 : ZMod 107933869)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 3), (8741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 3), (8741, 1)] : List FactorBlock).map factorBlockValue).prod) = 107933869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_8741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107933869) ^ 53966934 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 107933869) ^ 35977956 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 107933869) ^ 15419124 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 107933869) ^ 12348 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_112257799 : Nat.Prime 112257799 := by
  apply lucas_primality 112257799 (3 : ZMod 112257799)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18709633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18709633, 1)] : List FactorBlock).map factorBlockValue).prod) = 112257799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_18709633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 112257799) ^ 56128899 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112257799) ^ 37419266 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112257799) ^ 6 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_113251147 : Nat.Prime 113251147 := by
  apply lucas_primality 113251147 (2 : ZMod 113251147)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18875191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18875191, 1)] : List FactorBlock).map factorBlockValue).prod) = 113251147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_18875191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 113251147) ^ 56625573 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 113251147) ^ 37750382 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 113251147) ^ 6 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_127108873 : Nat.Prime 127108873 := by
  apply lucas_primality 127108873 (5 : ZMod 127108873)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (61, 1), (877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (61, 1), (877, 1)] : List FactorBlock).map factorBlockValue).prod) = 127108873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 127108873) ^ 63554436 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 127108873) ^ 42369624 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 127108873) ^ 11555352 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 127108873) ^ 2083752 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 127108873) ^ 144936 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_128568031 : Nat.Prime 128568031 := by
  apply lucas_primality 128568031 (3 : ZMod 128568031)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (91183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (91183, 1)] : List FactorBlock).map factorBlockValue).prod) = 128568031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_47
      · exact prime_oneHundredFortySevenEO_91183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 128568031) ^ 64284015 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 128568031) ^ 42856010 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 128568031) ^ 25713606 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 128568031) ^ 2735490 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 128568031) ^ 1410 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_151167007 : Nat.Prime 151167007 := by
  apply lucas_primality 151167007 (3 : ZMod 151167007)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (151, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (151, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) = 151167007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_151
      · exact prime_oneHundredFortySevenEO_18539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 151167007) ^ 75583503 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 151167007) ^ 50389002 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 151167007) ^ 1001106 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 151167007) ^ 8154 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_152592491 : Nat.Prime 152592491 := by
  apply lucas_primality 152592491 (6 : ZMod 152592491)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (71, 1), (7411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (71, 1), (7411, 1)] : List FactorBlock).map factorBlockValue).prod) = 152592491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_29
      · exact prime_oneHundredFortySevenEO_71
      · exact prime_oneHundredFortySevenEO_7411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 152592491) ^ 76296245 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 152592491) ^ 30518498 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 152592491) ^ 5261810 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 152592491) ^ 2149190 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 152592491) ^ 20590 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_166936741 : Nat.Prime 166936741 := by
  apply lucas_primality 166936741 (2 : ZMod 166936741)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2782279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2782279, 1)] : List FactorBlock).map factorBlockValue).prod) = 166936741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_2782279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 166936741) ^ 83468370 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 166936741) ^ 55645580 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 166936741) ^ 33387348 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 166936741) ^ 60 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_180926927 : Nat.Prime 180926927 := by
  apply lucas_primality 180926927 (5 : ZMod 180926927)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (90463463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (90463463, 1)] : List FactorBlock).map factorBlockValue).prod) = 180926927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_90463463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 180926927) ^ 90463463 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 180926927) ^ 2 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_189815837 : Nat.Prime 189815837 := by
  apply lucas_primality 189815837 (2 : ZMod 189815837)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2017, 1), (3361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2017, 1), (3361, 1)] : List FactorBlock).map factorBlockValue).prod) = 189815837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_2017
      · exact prime_oneHundredFortySevenEO_3361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 189815837) ^ 94907918 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 189815837) ^ 27116548 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 189815837) ^ 94108 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 189815837) ^ 56476 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_191938673 : Nat.Prime 191938673 := by
  apply lucas_primality 191938673 (3 : ZMod 191938673)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11996167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11996167, 1)] : List FactorBlock).map factorBlockValue).prod) = 191938673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_11996167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 191938673) ^ 95969336 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191938673) ^ 16 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_212008267 : Nat.Prime 212008267 := by
  apply lucas_primality 212008267 (2 : ZMod 212008267)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (436231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (436231, 1)] : List FactorBlock).map factorBlockValue).prod) = 212008267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_436231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 212008267) ^ 106004133 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 212008267) ^ 70669422 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 212008267) ^ 486 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_261525049 : Nat.Prime 261525049 := by
  apply lucas_primality 261525049 (13 : ZMod 261525049)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (10896877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (10896877, 1)] : List FactorBlock).map factorBlockValue).prod) = 261525049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_10896877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 261525049) ^ 130762524 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 261525049) ^ 87175016 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 261525049) ^ 24 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_278993839 : Nat.Prime 278993839 := by
  apply lucas_primality 278993839 (3 : ZMod 278993839)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (1256729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (1256729, 1)] : List FactorBlock).map factorBlockValue).prod) = 278993839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_37
      · exact prime_oneHundredFortySevenEO_1256729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 278993839) ^ 139496919 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 92997946 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 7540374 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 222 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_287395861 : Nat.Prime 287395861 := by
  apply lucas_primality 287395861 (6 : ZMod 287395861)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (137, 1), (34963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (137, 1), (34963, 1)] : List FactorBlock).map factorBlockValue).prod) = 287395861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_137
      · exact prime_oneHundredFortySevenEO_34963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 287395861) ^ 143697930 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 287395861) ^ 95798620 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 287395861) ^ 57479172 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 287395861) ^ 2097780 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 287395861) ^ 8220 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_292202129 : Nat.Prime 292202129 := by
  apply lucas_primality 292202129 (3 : ZMod 292202129)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (18262633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (18262633, 1)] : List FactorBlock).map factorBlockValue).prod) = 292202129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_18262633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 292202129) ^ 146101064 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 292202129) ^ 16 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_315113483 : Nat.Prime 315113483 := by
  apply lucas_primality 315113483 (2 : ZMod 315113483)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1531, 1), (102911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1531, 1), (102911, 1)] : List FactorBlock).map factorBlockValue).prod) = 315113483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_1531
      · exact prime_oneHundredFortySevenEO_102911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 315113483) ^ 157556741 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 315113483) ^ 205822 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 315113483) ^ 3062 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_331345633 : Nat.Prime 331345633 := by
  apply lucas_primality 331345633 (5 : ZMod 331345633)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (3451517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (3451517, 1)] : List FactorBlock).map factorBlockValue).prod) = 331345633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_3451517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 331345633) ^ 165672816 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 331345633) ^ 110448544 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 331345633) ^ 96 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_332072219 : Nat.Prime 332072219 := by
  apply lucas_primality 332072219 (2 : ZMod 332072219)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (869299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (869299, 1)] : List FactorBlock).map factorBlockValue).prod) = 332072219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_191
      · exact prime_oneHundredFortySevenEO_869299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 332072219) ^ 166036109 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 332072219) ^ 1738598 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 332072219) ^ 382 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_406236319 : Nat.Prime 406236319 := by
  apply lucas_primality 406236319 (3 : ZMod 406236319)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 3), (13781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 3), (13781, 1)] : List FactorBlock).map factorBlockValue).prod) = 406236319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_13781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 406236319) ^ 203118159 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 406236319) ^ 135412106 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 406236319) ^ 23896254 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 406236319) ^ 29478 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_418917271 : Nat.Prime 418917271 := by
  apply lucas_primality 418917271 (6 : ZMod 418917271)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13963909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13963909, 1)] : List FactorBlock).map factorBlockValue).prod) = 418917271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_13963909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 418917271) ^ 209458635 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 418917271) ^ 139639090 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 418917271) ^ 83783454 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 418917271) ^ 30 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_448619891 : Nat.Prime 448619891 := by
  apply lucas_primality 448619891 (6 : ZMod 448619891)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (631859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (631859, 1)] : List FactorBlock).map factorBlockValue).prod) = 448619891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_71
      · exact prime_oneHundredFortySevenEO_631859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 448619891) ^ 224309945 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 448619891) ^ 89723978 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 448619891) ^ 6318590 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 448619891) ^ 710 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_480610777 : Nat.Prime 480610777 := by
  apply lucas_primality 480610777 (5 : ZMod 480610777)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (1053971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (1053971, 1)] : List FactorBlock).map factorBlockValue).prod) = 480610777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_1053971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 480610777) ^ 240305388 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 480610777) ^ 160203592 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 480610777) ^ 25295304 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 480610777) ^ 456 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_484682431 : Nat.Prime 484682431 := by
  apply lucas_primality 484682431 (12 : ZMod 484682431)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89, 1), (167, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89, 1), (167, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 484682431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_89
      · exact prime_oneHundredFortySevenEO_167
      · exact prime_oneHundredFortySevenEO_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 484682431) ^ 242341215 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (12 : ZMod 484682431) ^ 161560810 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (12 : ZMod 484682431) ^ 96936486 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (12 : ZMod 484682431) ^ 5445870 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (12 : ZMod 484682431) ^ 2902290 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (12 : ZMod 484682431) ^ 445890 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_524679031 : Nat.Prime 524679031 := by
  apply lucas_primality 524679031 (3 : ZMod 524679031)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (89, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (89, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) = 524679031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_89
      · exact prime_oneHundredFortySevenEO_2113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 524679031) ^ 262339515 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679031) ^ 174893010 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679031) ^ 104935806 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679031) ^ 16925130 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679031) ^ 5895270 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679031) ^ 248310 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_533360389 : Nat.Prime 533360389 := by
  apply lucas_primality 533360389 (2 : ZMod 533360389)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (151, 1), (26759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (151, 1), (26759, 1)] : List FactorBlock).map factorBlockValue).prod) = 533360389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_151
      · exact prime_oneHundredFortySevenEO_26759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 533360389) ^ 266680194 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 533360389) ^ 177786796 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 533360389) ^ 48487308 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 533360389) ^ 3532188 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 533360389) ^ 19932 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_582142943 : Nat.Prime 582142943 := by
  apply lucas_primality 582142943 (5 : ZMod 582142943)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (599, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (599, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) = 582142943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_79
      · exact prime_oneHundredFortySevenEO_599
      · exact prime_oneHundredFortySevenEO_6151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 582142943) ^ 291071471 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 582142943) ^ 7368898 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 582142943) ^ 971858 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 582142943) ^ 94642 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_635991329 : Nat.Prime 635991329 := by
  apply lucas_primality 635991329 (3 : ZMod 635991329)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (43, 1), (66029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (43, 1), (66029, 1)] : List FactorBlock).map factorBlockValue).prod) = 635991329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_43
      · exact prime_oneHundredFortySevenEO_66029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 635991329) ^ 317995664 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 635991329) ^ 90855904 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 635991329) ^ 14790496 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 635991329) ^ 9632 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17203
      · exact prime_oneHundredFortySevenEO_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_859151537 : Nat.Prime 859151537 := by
  apply lucas_primality 859151537 (3 : ZMod 859151537)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5227, 1), (10273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5227, 1), (10273, 1)] : List FactorBlock).map factorBlockValue).prod) = 859151537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5227
      · exact prime_oneHundredFortySevenEO_10273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 859151537) ^ 429575768 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 859151537) ^ 164368 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 859151537) ^ 83632 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_882809359 : Nat.Prime 882809359 := by
  apply lucas_primality 882809359 (3 : ZMod 882809359)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (79, 1), (64223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (79, 1), (64223, 1)] : List FactorBlock).map factorBlockValue).prod) = 882809359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_29
      · exact prime_oneHundredFortySevenEO_79
      · exact prime_oneHundredFortySevenEO_64223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 882809359) ^ 441404679 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 882809359) ^ 294269786 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 882809359) ^ 30441702 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 882809359) ^ 11174802 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 882809359) ^ 13746 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1037719019 : Nat.Prime 1037719019 := by
  apply lucas_primality 1037719019 (2 : ZMod 1037719019)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (857, 1), (86491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (857, 1), (86491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1037719019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_857
      · exact prime_oneHundredFortySevenEO_86491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1037719019) ^ 518859509 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037719019) ^ 148245574 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037719019) ^ 1210874 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1037719019) ^ 11998 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1097965357 : Nat.Prime 1097965357 := by
  apply lucas_primality 1097965357 (2 : ZMod 1097965357)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (937, 1), (97649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (937, 1), (97649, 1)] : List FactorBlock).map factorBlockValue).prod) = 1097965357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_937
      · exact prime_oneHundredFortySevenEO_97649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1097965357) ^ 548982678 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097965357) ^ 365988452 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097965357) ^ 1171788 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097965357) ^ 11244 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1101126877 : Nat.Prime 1101126877 := by
  apply lucas_primality 1101126877 (2 : ZMod 1101126877)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (457, 1), (200789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (457, 1), (200789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101126877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_457
      · exact prime_oneHundredFortySevenEO_200789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1101126877) ^ 550563438 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 367042292 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 2409468 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 5484 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1124104987 : Nat.Prime 1124104987 := by
  apply lucas_primality 1124104987 (11 : ZMod 1124104987)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (20816759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (20816759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1124104987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_20816759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1124104987) ^ 562052493 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1124104987) ^ 374701662 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1124104987) ^ 54 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1151632039 : Nat.Prime 1151632039 := by
  apply lucas_primality 1151632039 (3 : ZMod 1151632039)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191938673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191938673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1151632039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_191938673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1151632039) ^ 575816019 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1151632039) ^ 383877346 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1151632039) ^ 6 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1153423387 : Nat.Prime 1153423387 := by
  apply lucas_primality 1153423387 (3 : ZMod 1153423387)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (31, 1), (108793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (31, 1), (108793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1153423387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_108793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1153423387) ^ 576711693 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1153423387) ^ 384474462 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1153423387) ^ 60706494 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1153423387) ^ 37207206 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1153423387) ^ 10602 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1269643913 : Nat.Prime 1269643913 := by
  apply lucas_primality 1269643913 (3 : ZMod 1269643913)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (241, 1), (38737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (241, 1), (38737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1269643913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_241
      · exact prime_oneHundredFortySevenEO_38737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1269643913) ^ 634821956 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269643913) ^ 74684936 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269643913) ^ 5268232 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269643913) ^ 32776 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1480338551 : Nat.Prime 1480338551 := by
  apply lucas_primality 1480338551 (23 : ZMod 1480338551)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (37, 1), (293, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (37, 1), (293, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1480338551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_37
      · exact prime_oneHundredFortySevenEO_293
      · exact prime_oneHundredFortySevenEO_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1480338551) ^ 740169275 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 1480338551) ^ 296067710 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 1480338551) ^ 40009150 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 1480338551) ^ 5052350 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 1480338551) ^ 542050 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1748677981 : Nat.Prime 1748677981 := by
  apply lucas_primality 1748677981 (6 : ZMod 1748677981)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (1567, 1), (2657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (1567, 1), (2657, 1)] : List FactorBlock).map factorBlockValue).prod) = 1748677981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_1567
      · exact prime_oneHundredFortySevenEO_2657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1748677981) ^ 874338990 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1748677981) ^ 582892660 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1748677981) ^ 349735596 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1748677981) ^ 249811140 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1748677981) ^ 1115940 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1748677981) ^ 658140 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1897376093 : Nat.Prime 1897376093 := by
  apply lucas_primality 1897376093 (2 : ZMod 1897376093)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5987, 1), (79229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5987, 1), (79229, 1)] : List FactorBlock).map factorBlockValue).prod) = 1897376093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5987
      · exact prime_oneHundredFortySevenEO_79229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1897376093) ^ 948688046 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1897376093) ^ 316916 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1897376093) ^ 23948 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2016230959 : Nat.Prime 2016230959 := by
  apply lucas_primality 2016230959 (3 : ZMod 2016230959)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (229, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (229, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2016230959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_229
      · exact prime_oneHundredFortySevenEO_69877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2016230959) ^ 1008115479 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 672076986 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 288032994 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 8804502 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 28854 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2092283509 : Nat.Prime 2092283509 := by
  apply lucas_primality 2092283509 (2 : ZMod 2092283509)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (43, 1), (579259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (43, 1), (579259, 1)] : List FactorBlock).map factorBlockValue).prod) = 2092283509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_43
      · exact prime_oneHundredFortySevenEO_579259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2092283509) ^ 1046141754 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2092283509) ^ 697427836 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2092283509) ^ 298897644 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2092283509) ^ 48657756 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2092283509) ^ 3612 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2367054121 : Nat.Prime 2367054121 := by
  apply lucas_primality 2367054121 (17 : ZMod 2367054121)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19725451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19725451, 1)] : List FactorBlock).map factorBlockValue).prod) = 2367054121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_19725451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2367054121) ^ 1183527060 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (17 : ZMod 2367054121) ^ 789018040 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (17 : ZMod 2367054121) ^ 473410824 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (17 : ZMod 2367054121) ^ 120 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2547184769 : Nat.Prime 2547184769 := by
  apply lucas_primality 2547184769 (3 : ZMod 2547184769)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (19899881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (19899881, 1)] : List FactorBlock).map factorBlockValue).prod) = 2547184769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_19899881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2547184769) ^ 1273592384 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2547184769) ^ 128 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2579046059 : Nat.Prime 2579046059 := by
  apply lucas_primality 2579046059 (2 : ZMod 2579046059)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (2145629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (2145629, 1)] : List FactorBlock).map factorBlockValue).prod) = 2579046059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_601
      · exact prime_oneHundredFortySevenEO_2145629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2579046059) ^ 1289523029 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579046059) ^ 4291258 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579046059) ^ 1202 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2673164471 : Nat.Prime 2673164471 := by
  apply lucas_primality 2673164471 (19 : ZMod 2673164471)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (433, 1), (617359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (433, 1), (617359, 1)] : List FactorBlock).map factorBlockValue).prod) = 2673164471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_433
      · exact prime_oneHundredFortySevenEO_617359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 2673164471) ^ 1336582235 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (19 : ZMod 2673164471) ^ 534632894 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (19 : ZMod 2673164471) ^ 6173590 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (19 : ZMod 2673164471) ^ 4330 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2947692823 : Nat.Prime 2947692823 := by
  apply lucas_primality 2947692823 (3 : ZMod 2947692823)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (3586001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (3586001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2947692823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_137
      · exact prime_oneHundredFortySevenEO_3586001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2947692823) ^ 1473846411 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2947692823) ^ 982564274 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2947692823) ^ 21516006 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2947692823) ^ 822 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3188388937 : Nat.Prime 3188388937 := by
  apply lucas_primality 3188388937 (5 : ZMod 3188388937)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (31, 1), (283, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (31, 1), (283, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 3188388937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_283
      · exact prime_oneHundredFortySevenEO_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3188388937) ^ 1594194468 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3188388937) ^ 1062796312 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3188388937) ^ 167809944 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3188388937) ^ 102851256 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3188388937) ^ 11266392 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3188388937) ^ 4000488 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3474609461 : Nat.Prime 3474609461 := by
  apply lucas_primality 3474609461 (2 : ZMod 3474609461)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1979, 1), (12541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1979, 1), (12541, 1)] : List FactorBlock).map factorBlockValue).prod) = 3474609461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_1979
      · exact prime_oneHundredFortySevenEO_12541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3474609461) ^ 1737304730 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3474609461) ^ 694921892 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3474609461) ^ 496372780 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3474609461) ^ 1755740 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3474609461) ^ 277060 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3584413829 : Nat.Prime 3584413829 := by
  apply lucas_primality 3584413829 (2 : ZMod 3584413829)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (19066031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (19066031, 1)] : List FactorBlock).map factorBlockValue).prod) = 3584413829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_47
      · exact prime_oneHundredFortySevenEO_19066031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3584413829) ^ 1792206914 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3584413829) ^ 76264124 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3584413829) ^ 188 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3602199017 : Nat.Prime 3602199017 := by
  apply lucas_primality 3602199017 (3 : ZMod 3602199017)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (73, 1), (617, 1), (769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (73, 1), (617, 1), (769, 1)] : List FactorBlock).map factorBlockValue).prod) = 3602199017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_73
      · exact prime_oneHundredFortySevenEO_617
      · exact prime_oneHundredFortySevenEO_769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3602199017) ^ 1801099508 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3602199017) ^ 277092232 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3602199017) ^ 49345192 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3602199017) ^ 5838248 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3602199017) ^ 4684264 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3728286137 : Nat.Prime 3728286137 := by
  apply lucas_primality 3728286137 (3 : ZMod 3728286137)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (227, 1), (2053021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (227, 1), (2053021, 1)] : List FactorBlock).map factorBlockValue).prod) = 3728286137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_227
      · exact prime_oneHundredFortySevenEO_2053021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3728286137) ^ 1864143068 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3728286137) ^ 16424168 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3728286137) ^ 1816 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3907206839 : Nat.Prime 3907206839 := by
  apply lucas_primality 3907206839 (7 : ZMod 3907206839)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (557, 1), (3507367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (557, 1), (3507367, 1)] : List FactorBlock).map factorBlockValue).prod) = 3907206839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_557
      · exact prime_oneHundredFortySevenEO_3507367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3907206839) ^ 1953603419 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3907206839) ^ 7014734 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3907206839) ^ 1114 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4153697519 : Nat.Prime 4153697519 := by
  apply lucas_primality 4153697519 (11 : ZMod 4153697519)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (101, 1), (281683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (101, 1), (281683, 1)] : List FactorBlock).map factorBlockValue).prod) = 4153697519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_73
      · exact prime_oneHundredFortySevenEO_101
      · exact prime_oneHundredFortySevenEO_281683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4153697519) ^ 2076848759 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4153697519) ^ 56899966 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4153697519) ^ 41125718 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4153697519) ^ 14746 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5087930633 : Nat.Prime 5087930633 := by
  apply lucas_primality 5087930633 (3 : ZMod 5087930633)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (635991329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (635991329, 1)] : List FactorBlock).map factorBlockValue).prod) = 5087930633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_635991329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5087930633) ^ 2543965316 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5087930633) ^ 8 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5200598791 : Nat.Prime 5200598791 := by
  apply lucas_primality 5200598791 (6 : ZMod 5200598791)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (181, 1), (106417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (181, 1), (106417, 1)] : List FactorBlock).map factorBlockValue).prod) = 5200598791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_181
      · exact prime_oneHundredFortySevenEO_106417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5200598791) ^ 2600299395 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 5200598791) ^ 1733532930 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 5200598791) ^ 1040119758 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 5200598791) ^ 28732590 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 5200598791) ^ 48870 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5458268173 : Nat.Prime 5458268173 := by
  apply lucas_primality 5458268173 (5 : ZMod 5458268173)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (41, 1), (226409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (41, 1), (226409, 1)] : List FactorBlock).map factorBlockValue).prod) = 5458268173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_41
      · exact prime_oneHundredFortySevenEO_226409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5458268173) ^ 2729134086 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5458268173) ^ 1819422724 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5458268173) ^ 779752596 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5458268173) ^ 133128492 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5458268173) ^ 24108 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5626928773 : Nat.Prime 5626928773 := by
  apply lucas_primality 5626928773 (2 : ZMod 5626928773)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (37, 1), (673, 1), (6277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (37, 1), (673, 1), (6277, 1)] : List FactorBlock).map factorBlockValue).prod) = 5626928773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_37
      · exact prime_oneHundredFortySevenEO_673
      · exact prime_oneHundredFortySevenEO_6277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5626928773) ^ 2813464386 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5626928773) ^ 1875642924 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5626928773) ^ 152079156 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5626928773) ^ 8360964 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5626928773) ^ 896436 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6085218281 : Nat.Prime 6085218281 := by
  apply lucas_primality 6085218281 (3 : ZMod 6085218281)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (271, 1), (561367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (271, 1), (561367, 1)] : List FactorBlock).map factorBlockValue).prod) = 6085218281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_271
      · exact prime_oneHundredFortySevenEO_561367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6085218281) ^ 3042609140 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6085218281) ^ 1217043656 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6085218281) ^ 22454680 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6085218281) ^ 10840 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_311
      · exact prime_oneHundredFortySevenEO_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6587792143 : Nat.Prime 6587792143 := by
  apply lucas_primality 6587792143 (3 : ZMod 6587792143)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1097965357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1097965357, 1)] : List FactorBlock).map factorBlockValue).prod) = 6587792143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_1097965357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6587792143) ^ 3293896071 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6587792143) ^ 2195930714 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6587792143) ^ 6 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6744629923 : Nat.Prime 6744629923 := by
  apply lucas_primality 6744629923 (3 : ZMod 6744629923)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1124104987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1124104987, 1)] : List FactorBlock).map factorBlockValue).prod) = 6744629923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_1124104987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6744629923) ^ 3372314961 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6744629923) ^ 2248209974 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6744629923) ^ 6 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_8135250713 : Nat.Prime 8135250713 := by
  apply lucas_primality 8135250713 (3 : ZMod 8135250713)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (179, 1), (541, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (179, 1), (541, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod) = 8135250713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_179
      · exact prime_oneHundredFortySevenEO_541
      · exact prime_oneHundredFortySevenEO_10501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8135250713) ^ 4067625356 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 8135250713) ^ 45448328 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 8135250713) ^ 15037432 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 8135250713) ^ 774712 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_8307395039 : Nat.Prime 8307395039 := by
  apply lucas_primality 8307395039 (11 : ZMod 8307395039)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4153697519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4153697519, 1)] : List FactorBlock).map factorBlockValue).prod) = 8307395039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_4153697519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 8307395039) ^ 4153697519 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 8307395039) ^ 2 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_8592847253 : Nat.Prime 8592847253 := by
  apply lucas_primality 8592847253 (2 : ZMod 8592847253)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (373, 1), (523571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (373, 1), (523571, 1)] : List FactorBlock).map factorBlockValue).prod) = 8592847253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_373
      · exact prime_oneHundredFortySevenEO_523571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8592847253) ^ 4296423626 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8592847253) ^ 781167932 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8592847253) ^ 23037124 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8592847253) ^ 16412 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_9009417817 : Nat.Prime 9009417817 := by
  apply lucas_primality 9009417817 (5 : ZMod 9009417817)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (17875829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (17875829, 1)] : List FactorBlock).map factorBlockValue).prod) = 9009417817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_17875829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9009417817) ^ 4504708908 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 9009417817) ^ 3003139272 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 9009417817) ^ 1287059688 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 9009417817) ^ 504 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_11889160219 : Nat.Prime 11889160219 := by
  apply lucas_primality 11889160219 (3 : ZMod 11889160219)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (29, 1), (1752013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (29, 1), (1752013, 1)] : List FactorBlock).map factorBlockValue).prod) = 11889160219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_29
      · exact prime_oneHundredFortySevenEO_1752013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11889160219) ^ 5944580109 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11889160219) ^ 3963053406 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11889160219) ^ 914550786 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11889160219) ^ 409971042 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11889160219) ^ 6786 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_15408878399 : Nat.Prime 15408878399 := by
  apply lucas_primality 15408878399 (13 : ZMod 15408878399)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (431, 1), (244873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (431, 1), (244873, 1)] : List FactorBlock).map factorBlockValue).prod) = 15408878399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_73
      · exact prime_oneHundredFortySevenEO_431
      · exact prime_oneHundredFortySevenEO_244873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 15408878399) ^ 7704439199 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 15408878399) ^ 211080526 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 15408878399) ^ 35751458 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 15408878399) ^ 62926 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_19172900827 : Nat.Prime 19172900827 := by
  apply lucas_primality 19172900827 (2 : ZMod 19172900827)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1381, 1), (257099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1381, 1), (257099, 1)] : List FactorBlock).map factorBlockValue).prod) = 19172900827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_1381
      · exact prime_oneHundredFortySevenEO_257099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19172900827) ^ 9586450413 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19172900827) ^ 6390966942 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19172900827) ^ 13883346 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19172900827) ^ 74574 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_20288258719 : Nat.Prime 20288258719 := by
  apply lucas_primality 20288258719 (3 : ZMod 20288258719)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (461, 1), (80603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (461, 1), (80603, 1)] : List FactorBlock).map factorBlockValue).prod) = 20288258719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_461
      · exact prime_oneHundredFortySevenEO_80603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20288258719) ^ 10144129359 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 6762752906 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 2898322674 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 1560635286 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 44009238 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 251706 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_23768183623 : Nat.Prime 23768183623 := by
  apply lucas_primality 23768183623 (6 : ZMod 23768183623)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (593, 1), (19141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (593, 1), (19141, 1)] : List FactorBlock).map factorBlockValue).prod) = 23768183623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_349
      · exact prime_oneHundredFortySevenEO_593
      · exact prime_oneHundredFortySevenEO_19141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23768183623) ^ 11884091811 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 23768183623) ^ 7922727874 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 23768183623) ^ 68103678 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 23768183623) ^ 40081254 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 23768183623) ^ 1241742 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_23855439659 : Nat.Prime 23855439659 := by
  apply lucas_primality 23855439659 (2 : ZMod 23855439659)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13591, 1), (877619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13591, 1), (877619, 1)] : List FactorBlock).map factorBlockValue).prod) = 23855439659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_13591
      · exact prime_oneHundredFortySevenEO_877619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23855439659) ^ 11927719829 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23855439659) ^ 1755238 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 23855439659) ^ 27182 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_24286998233 : Nat.Prime 24286998233 := by
  apply lucas_primality 24286998233 (3 : ZMod 24286998233)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (61, 1), (1777, 1), (4001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (61, 1), (1777, 1), (4001, 1)] : List FactorBlock).map factorBlockValue).prod) = 24286998233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_1777
      · exact prime_oneHundredFortySevenEO_4001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24286998233) ^ 12143499116 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 24286998233) ^ 3469571176 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 24286998233) ^ 398147512 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 24286998233) ^ 13667416 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 24286998233) ^ 6070232 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_24570248051 : Nat.Prime 24570248051 := by
  apply lucas_primality 24570248051 (10 : ZMod 24570248051)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (25863419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (25863419, 1)] : List FactorBlock).map factorBlockValue).prod) = 24570248051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_25863419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 24570248051) ^ 12285124025 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 4914049610 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 1293170950 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 950 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_24652101373 : Nat.Prime 24652101373 := by
  apply lucas_primality 24652101373 (2 : ZMod 24652101373)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (599, 1), (3429619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (599, 1), (3429619, 1)] : List FactorBlock).map factorBlockValue).prod) = 24652101373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_599
      · exact prime_oneHundredFortySevenEO_3429619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24652101373) ^ 12326050686 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24652101373) ^ 8217367124 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24652101373) ^ 41155428 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24652101373) ^ 7188 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_26430404149 : Nat.Prime 26430404149 := by
  apply lucas_primality 26430404149 (6 : ZMod 26430404149)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (109, 1), (229, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (109, 1), (229, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) = 26430404149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_67
      · exact prime_oneHundredFortySevenEO_109
      · exact prime_oneHundredFortySevenEO_229
      · exact prime_oneHundredFortySevenEO_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26430404149) ^ 13215202074 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26430404149) ^ 8810134716 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26430404149) ^ 394483644 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26430404149) ^ 242480772 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26430404149) ^ 115416612 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26430404149) ^ 60205932 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_30566217229 : Nat.Prime 30566217229 := by
  apply lucas_primality 30566217229 (2 : ZMod 30566217229)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2547184769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2547184769, 1)] : List FactorBlock).map factorBlockValue).prod) = 30566217229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_2547184769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30566217229) ^ 15283108614 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30566217229) ^ 10188739076 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30566217229) ^ 12 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_33164393279 : Nat.Prime 33164393279 := by
  apply lucas_primality 33164393279 (23 : ZMod 33164393279)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (113, 1), (197, 1), (24029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (113, 1), (197, 1), (24029, 1)] : List FactorBlock).map factorBlockValue).prod) = 33164393279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_113
      · exact prime_oneHundredFortySevenEO_197
      · exact prime_oneHundredFortySevenEO_24029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 33164393279) ^ 16582196639 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 33164393279) ^ 1069819138 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 33164393279) ^ 293490206 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 33164393279) ^ 168347174 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 33164393279) ^ 1380182 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_49352117621 : Nat.Prime 49352117621 := by
  apply lucas_primality 49352117621 (2 : ZMod 49352117621)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (189815837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (189815837, 1)] : List FactorBlock).map factorBlockValue).prod) = 49352117621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_189815837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49352117621) ^ 24676058810 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49352117621) ^ 9870423524 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49352117621) ^ 3796316740 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49352117621) ^ 260 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_53030034293 : Nat.Prime 53030034293 := by
  apply lucas_primality 53030034293 (2 : ZMod 53030034293)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4441, 1), (2985253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4441, 1), (2985253, 1)] : List FactorBlock).map factorBlockValue).prod) = 53030034293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_4441
      · exact prime_oneHundredFortySevenEO_2985253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53030034293) ^ 26515017146 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 53030034293) ^ 11941012 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 53030034293) ^ 17764 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_53530439189 : Nat.Prime 53530439189 := by
  apply lucas_primality 53530439189 (2 : ZMod 53530439189)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (41, 1), (19200301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (41, 1), (19200301, 1)] : List FactorBlock).map factorBlockValue).prod) = 53530439189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_41
      · exact prime_oneHundredFortySevenEO_19200301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53530439189) ^ 26765219594 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 53530439189) ^ 3148849364 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 53530439189) ^ 1305620468 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 53530439189) ^ 2788 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_55966360487 : Nat.Prime 55966360487 := by
  apply lucas_primality 55966360487 (5 : ZMod 55966360487)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (261525049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (261525049, 1)] : List FactorBlock).map factorBlockValue).prod) = 55966360487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_107
      · exact prime_oneHundredFortySevenEO_261525049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 55966360487) ^ 27983180243 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 55966360487) ^ 523050098 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 55966360487) ^ 214 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_61630287739 : Nat.Prime 61630287739 := by
  apply lucas_primality 61630287739 (2 : ZMod 61630287739)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (331345633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (331345633, 1)] : List FactorBlock).map factorBlockValue).prod) = 61630287739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_331345633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61630287739) ^ 30815143869 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61630287739) ^ 20543429246 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61630287739) ^ 1988073798 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61630287739) ^ 186 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_69914037331 : Nat.Prime 69914037331 := by
  apply lucas_primality 69914037331 (3 : ZMod 69914037331)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (503, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (503, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod) = 69914037331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_503
      · exact prime_oneHundredFortySevenEO_514793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69914037331) ^ 34957018665 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 69914037331) ^ 23304679110 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 69914037331) ^ 13982807466 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 69914037331) ^ 138994110 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 69914037331) ^ 135810 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_79139395873 : Nat.Prime 79139395873 := by
  apply lucas_primality 79139395873 (5 : ZMod 79139395873)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (91596523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (91596523, 1)] : List FactorBlock).map factorBlockValue).prod) = 79139395873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_91596523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 79139395873) ^ 39569697936 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 79139395873) ^ 26379798624 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 79139395873) ^ 864 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_109533929059 : Nat.Prime 109533929059 := by
  apply lucas_primality 109533929059 (2 : ZMod 109533929059)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6085218281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6085218281, 1)] : List FactorBlock).map factorBlockValue).prod) = 109533929059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_6085218281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 109533929059) ^ 54766964529 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 109533929059) ^ 36511309686 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 109533929059) ^ 18 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_112653552233 : Nat.Prime 112653552233 := by
  apply lucas_primality 112653552233 (3 : ZMod 112653552233)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (19, 1), (57010907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (19, 1), (57010907, 1)] : List FactorBlock).map factorBlockValue).prod) = 112653552233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_57010907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 112653552233) ^ 56326776116 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112653552233) ^ 8665657864 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112653552233) ^ 5929134328 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112653552233) ^ 1976 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_89
      · exact prime_oneHundredFortySevenEO_373
      · exact prime_oneHundredFortySevenEO_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_166553936533 : Nat.Prime 166553936533 := by
  apply lucas_primality 166553936533 (2 : ZMod 166553936533)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (71, 1), (21720649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (71, 1), (21720649, 1)] : List FactorBlock).map factorBlockValue).prod) = 166553936533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_71
      · exact prime_oneHundredFortySevenEO_21720649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 166553936533) ^ 83276968266 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 166553936533) ^ 55517978844 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 166553936533) ^ 2345830092 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 166553936533) ^ 7668 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_171917100917 : Nat.Prime 171917100917 := by
  apply lucas_primality 171917100917 (2 : ZMod 171917100917)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3907206839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3907206839, 1)] : List FactorBlock).map factorBlockValue).prod) = 171917100917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_3907206839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 171917100917) ^ 85958550458 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 171917100917) ^ 15628827356 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 171917100917) ^ 44 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_183497690903 : Nat.Prime 183497690903 := by
  apply lucas_primality 183497690903 (5 : ZMod 183497690903)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (67, 1), (3559, 1), (16729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (67, 1), (3559, 1), (16729, 1)] : List FactorBlock).map factorBlockValue).prod) = 183497690903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_67
      · exact prime_oneHundredFortySevenEO_3559
      · exact prime_oneHundredFortySevenEO_16729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 183497690903) ^ 91748845451 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 183497690903) ^ 7978160474 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 183497690903) ^ 2738771506 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 183497690903) ^ 51558778 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 183497690903) ^ 10968838 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_201897644693 : Nat.Prime 201897644693 := by
  apply lucas_primality 201897644693 (2 : ZMod 201897644693)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (223, 1), (421, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (223, 1), (421, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) = 201897644693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_29
      · exact prime_oneHundredFortySevenEO_223
      · exact prime_oneHundredFortySevenEO_421
      · exact prime_oneHundredFortySevenEO_18539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 201897644693) ^ 100948822346 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 201897644693) ^ 6961987748 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 201897644693) ^ 905370604 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 201897644693) ^ 479566852 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 201897644693) ^ 10890428 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_222050782651 : Nat.Prime 222050782651 := by
  apply lucas_primality 222050782651 (11 : ZMod 222050782651)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1480338551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1480338551, 1)] : List FactorBlock).map factorBlockValue).prod) = 222050782651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_1480338551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 222050782651) ^ 111025391325 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 222050782651) ^ 74016927550 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 222050782651) ^ 44410156530 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 222050782651) ^ 150 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_241716657139 : Nat.Prime 241716657139 := by
  apply lucas_primality 241716657139 (3 : ZMod 241716657139)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (317, 1), (1061, 1), (10889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (317, 1), (1061, 1), (10889, 1)] : List FactorBlock).map factorBlockValue).prod) = 241716657139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_317
      · exact prime_oneHundredFortySevenEO_1061
      · exact prime_oneHundredFortySevenEO_10889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 241716657139) ^ 120858328569 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 241716657139) ^ 80572219046 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 241716657139) ^ 21974241558 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 241716657139) ^ 762513114 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 241716657139) ^ 227819658 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 241716657139) ^ 22198242 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_243363507077 : Nat.Prime 243363507077 := by
  apply lucas_primality 243363507077 (2 : ZMod 243363507077)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1871, 1), (32517839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1871, 1), (32517839, 1)] : List FactorBlock).map factorBlockValue).prod) = 243363507077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_1871
      · exact prime_oneHundredFortySevenEO_32517839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 243363507077) ^ 121681753538 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 243363507077) ^ 130071356 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 243363507077) ^ 7484 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_274916209307 : Nat.Prime 274916209307 := by
  apply lucas_primality 274916209307 (2 : ZMod 274916209307)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (71, 1), (157, 1), (34159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (71, 1), (157, 1), (34159, 1)] : List FactorBlock).map factorBlockValue).prod) = 274916209307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_71
      · exact prime_oneHundredFortySevenEO_157
      · exact prime_oneHundredFortySevenEO_34159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 274916209307) ^ 137458104653 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 274916209307) ^ 14469274174 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 274916209307) ^ 3872059286 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 274916209307) ^ 1751058658 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 274916209307) ^ 8048134 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_3931
      · exact prime_oneHundredFortySevenEO_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_360123441473 : Nat.Prime 360123441473 := by
  apply lucas_primality 360123441473 (3 : ZMod 360123441473)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5626928773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5626928773, 1)] : List FactorBlock).map factorBlockValue).prod) = 360123441473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5626928773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 360123441473) ^ 180061720736 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 360123441473) ^ 64 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_364845133117 : Nat.Prime 364845133117 := by
  apply lucas_primality 364845133117 (2 : ZMod 364845133117)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (61, 1), (67, 1), (826571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (61, 1), (67, 1), (826571, 1)] : List FactorBlock).map factorBlockValue).prod) = 364845133117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_67
      · exact prime_oneHundredFortySevenEO_826571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 364845133117) ^ 182422566558 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 364845133117) ^ 121615044372 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 364845133117) ^ 5981067756 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 364845133117) ^ 5445449748 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 364845133117) ^ 441396 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_366995381807 : Nat.Prime 366995381807 := by
  apply lucas_primality 366995381807 (5 : ZMod 366995381807)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (183497690903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (183497690903, 1)] : List FactorBlock).map factorBlockValue).prod) = 366995381807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_183497690903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 366995381807) ^ 183497690903 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 366995381807) ^ 2 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_518968924567 : Nat.Prime 518968924567 := by
  apply lucas_primality 518968924567 (3 : ZMod 518968924567)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (5087930633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (5087930633, 1)] : List FactorBlock).map factorBlockValue).prod) = 518968924567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_5087930633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 518968924567) ^ 259484462283 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 518968924567) ^ 172989641522 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 518968924567) ^ 30527583798 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 518968924567) ^ 102 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_594685418827 : Nat.Prime 594685418827 := by
  apply lucas_primality 594685418827 (2 : ZMod 594685418827)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3259, 1), (30412469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3259, 1), (30412469, 1)] : List FactorBlock).map factorBlockValue).prod) = 594685418827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_3259
      · exact prime_oneHundredFortySevenEO_30412469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 594685418827) ^ 297342709413 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 594685418827) ^ 198228472942 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 594685418827) ^ 182474814 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 594685418827) ^ 19554 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_597737766523 : Nat.Prime 597737766523 := by
  apply lucas_primality 597737766523 (5 : ZMod 597737766523)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (71, 1), (107933869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (71, 1), (107933869, 1)] : List FactorBlock).map factorBlockValue).prod) = 597737766523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_71
      · exact prime_oneHundredFortySevenEO_107933869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 597737766523) ^ 298868883261 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 597737766523) ^ 199245922174 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 597737766523) ^ 45979828194 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 597737766523) ^ 8418841782 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 597737766523) ^ 5538 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_674756143339 : Nat.Prime 674756143339 := by
  apply lucas_primality 674756143339 (3 : ZMod 674756143339)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 2), (313, 1), (80039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 2), (313, 1), (80039, 1)] : List FactorBlock).map factorBlockValue).prod) = 674756143339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_67
      · exact prime_oneHundredFortySevenEO_313
      · exact prime_oneHundredFortySevenEO_80039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 674756143339) ^ 337378071669 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 224918714446 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 10070987214 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 2155770426 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 8430342 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_720439803401 : Nat.Prime 720439803401 := by
  apply lucas_primality 720439803401 (3 : ZMod 720439803401)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (3602199017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (3602199017, 1)] : List FactorBlock).map factorBlockValue).prod) = 720439803401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_3602199017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 720439803401) ^ 360219901700 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 720439803401) ^ 144087960680 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 720439803401) ^ 200 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_929777891069 : Nat.Prime 929777891069 := by
  apply lucas_primality 929777891069 (2 : ZMod 929777891069)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (241, 1), (74192299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (241, 1), (74192299, 1)] : List FactorBlock).map factorBlockValue).prod) = 929777891069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_241
      · exact prime_oneHundredFortySevenEO_74192299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 929777891069) ^ 464888945534 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 929777891069) ^ 71521376236 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 929777891069) ^ 3857999548 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 929777891069) ^ 12532 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1006746677977 : Nat.Prime 1006746677977 := by
  apply lucas_primality 1006746677977 (7 : ZMod 1006746677977)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (103, 1), (353, 1), (88747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (103, 1), (353, 1), (88747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1006746677977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_103
      · exact prime_oneHundredFortySevenEO_353
      · exact prime_oneHundredFortySevenEO_88747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1006746677977) ^ 503373338988 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1006746677977) ^ 335582225992 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1006746677977) ^ 77442052152 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1006746677977) ^ 9774239592 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1006746677977) ^ 2851973592 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1006746677977) ^ 11344008 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1039251385787 : Nat.Prime 1039251385787 := by
  apply lucas_primality 1039251385787 (2 : ZMod 1039251385787)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (30566217229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (30566217229, 1)] : List FactorBlock).map factorBlockValue).prod) = 1039251385787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_30566217229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1039251385787) ^ 519625692893 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039251385787) ^ 61132434458 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039251385787) ^ 34 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1057198211803 : Nat.Prime 1057198211803 := by
  apply lucas_primality 1057198211803 (3 : ZMod 1057198211803)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (1151632039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (1151632039, 1)] : List FactorBlock).map factorBlockValue).prod) = 1057198211803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_1151632039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1057198211803) ^ 528599105901 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1057198211803) ^ 352399403934 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1057198211803) ^ 62188130106 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1057198211803) ^ 918 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1109345179303 : Nat.Prime 1109345179303 := by
  apply lucas_primality 1109345179303 (3 : ZMod 1109345179303)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61630287739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61630287739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109345179303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_61630287739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1109345179303) ^ 554672589651 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1109345179303) ^ 369781726434 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1109345179303) ^ 18 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1137600946049 : Nat.Prime 1137600946049 := by
  apply lucas_primality 1137600946049 (3 : ZMod 1137600946049)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (1269643913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (1269643913, 1)] : List FactorBlock).map factorBlockValue).prod) = 1137600946049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_1269643913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1137600946049) ^ 568800473024 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137600946049) ^ 162514420864 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137600946049) ^ 896 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1375336807337 : Nat.Prime 1375336807337 := by
  apply lucas_primality 1375336807337 (3 : ZMod 1375336807337)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (171917100917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (171917100917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1375336807337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_171917100917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1375336807337) ^ 687668403668 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1375336807337) ^ 8 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1500099095153 : Nat.Prime 1500099095153 := by
  apply lucas_primality 1500099095153 (3 : ZMod 1500099095153)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (31, 1), (4283, 1), (14411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (31, 1), (4283, 1), (14411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1500099095153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_4283
      · exact prime_oneHundredFortySevenEO_14411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1500099095153) ^ 750049547576 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1500099095153) ^ 214299870736 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1500099095153) ^ 48390293392 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1500099095153) ^ 350244944 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1500099095153) ^ 104094032 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1504911844199 : Nat.Prime 1504911844199 := by
  apply lucas_primality 1504911844199 (7 : ZMod 1504911844199)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (136471, 1), (787667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (136471, 1), (787667, 1)] : List FactorBlock).map factorBlockValue).prod) = 1504911844199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_136471
      · exact prime_oneHundredFortySevenEO_787667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1504911844199) ^ 752455922099 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1504911844199) ^ 214987406314 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1504911844199) ^ 11027338 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1504911844199) ^ 1910594 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1509002800313 : Nat.Prime 1509002800313 := by
  apply lucas_primality 1509002800313 (5 : ZMod 1509002800313)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1787, 1), (15079171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1787, 1), (15079171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1509002800313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_1787
      · exact prime_oneHundredFortySevenEO_15079171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1509002800313) ^ 754501400156 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1509002800313) ^ 215571828616 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1509002800313) ^ 844433576 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1509002800313) ^ 100072 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1579267763873 : Nat.Prime 1579267763873 := by
  apply lucas_primality 1579267763873 (3 : ZMod 1579267763873)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (49352117621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (49352117621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1579267763873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_49352117621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1579267763873) ^ 789633881936 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579267763873) ^ 32 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2371919671021 : Nat.Prime 2371919671021 := by
  apply lucas_primality 2371919671021 (2 : ZMod 2371919671021)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (53, 1), (16097, 1), (46337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (53, 1), (16097, 1), (46337, 1)] : List FactorBlock).map factorBlockValue).prod) = 2371919671021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_53
      · exact prime_oneHundredFortySevenEO_16097
      · exact prime_oneHundredFortySevenEO_46337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2371919671021) ^ 1185959835510 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2371919671021) ^ 790639890340 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2371919671021) ^ 474383934204 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2371919671021) ^ 44753201340 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2371919671021) ^ 147351660 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2371919671021) ^ 51188460 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4232894525309 : Nat.Prime 4232894525309 := by
  apply lucas_primality 4232894525309 (2 : ZMod 4232894525309)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3793, 1), (278993839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3793, 1), (278993839, 1)] : List FactorBlock).map factorBlockValue).prod) = 4232894525309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3793
      · exact prime_oneHundredFortySevenEO_278993839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4232894525309) ^ 2116447262654 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4232894525309) ^ 1115975356 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4232894525309) ^ 15172 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4375221181031 : Nat.Prime 4375221181031 := by
  apply lucas_primality 4375221181031 (14 : ZMod 4375221181031)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (2016230959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (2016230959, 1)] : List FactorBlock).map factorBlockValue).prod) = 4375221181031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_2016230959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4375221181031) ^ 2187610590515 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 875044236206 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 625031597290 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 141136167130 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 2170 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4437380717213 : Nat.Prime 4437380717213 := by
  apply lucas_primality 4437380717213 (2 : ZMod 4437380717213)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1109345179303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1109345179303, 1)] : List FactorBlock).map factorBlockValue).prod) = 4437380717213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_1109345179303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4437380717213) ^ 2218690358606 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4437380717213) ^ 4 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5207265435319 : Nat.Prime 5207265435319 := by
  apply lucas_primality 5207265435319 (3 : ZMod 5207265435319)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (8592847253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (8592847253, 1)] : List FactorBlock).map factorBlockValue).prod) = 5207265435319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_101
      · exact prime_oneHundredFortySevenEO_8592847253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5207265435319) ^ 2603632717659 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5207265435319) ^ 1735755145106 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5207265435319) ^ 51557083518 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5207265435319) ^ 606 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5246525095081 : Nat.Prime 5246525095081 := by
  apply lucas_primality 5246525095081 (11 : ZMod 5246525095081)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (1259, 1), (2042753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (1259, 1), (2042753, 1)] : List FactorBlock).map factorBlockValue).prod) = 5246525095081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_1259
      · exact prime_oneHundredFortySevenEO_2042753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5246525095081) ^ 2623262547540 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5246525095081) ^ 1748841698360 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5246525095081) ^ 1049305019016 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5246525095081) ^ 308619123240 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5246525095081) ^ 4167216120 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5246525095081) ^ 2568360 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5760996460301 : Nat.Prime 5760996460301 := by
  apply lucas_primality 5760996460301 (2 : ZMod 5760996460301)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (139, 1), (239, 1), (1734143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (139, 1), (239, 1), (1734143, 1)] : List FactorBlock).map factorBlockValue).prod) = 5760996460301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_139
      · exact prime_oneHundredFortySevenEO_239
      · exact prime_oneHundredFortySevenEO_1734143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5760996460301) ^ 2880498230150 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5760996460301) ^ 1152199292060 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5760996460301) ^ 41446017700 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5760996460301) ^ 24104587700 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5760996460301) ^ 3322100 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_8097073720069 : Nat.Prime 8097073720069 := by
  apply lucas_primality 8097073720069 (2 : ZMod 8097073720069)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (674756143339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (674756143339, 1)] : List FactorBlock).map factorBlockValue).prod) = 8097073720069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_674756143339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8097073720069) ^ 4048536860034 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8097073720069) ^ 2699024573356 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8097073720069) ^ 12 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_9523800417107 : Nat.Prime 9523800417107 := by
  apply lucas_primality 9523800417107 (2 : ZMod 9523800417107)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (457, 1), (7691, 1), (1354819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (457, 1), (7691, 1), (1354819, 1)] : List FactorBlock).map factorBlockValue).prod) = 9523800417107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_457
      · exact prime_oneHundredFortySevenEO_7691
      · exact prime_oneHundredFortySevenEO_1354819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9523800417107) ^ 4761900208553 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9523800417107) ^ 20839825858 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9523800417107) ^ 1238304566 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9523800417107) ^ 7029574 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_9539040975421 : Nat.Prime 9539040975421 := by
  apply lucas_primality 9539040975421 (2 : ZMod 9539040975421)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (19, 2), (499, 1), (80233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (19, 2), (499, 1), (80233, 1)] : List FactorBlock).map factorBlockValue).prod) = 9539040975421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_499
      · exact prime_oneHundredFortySevenEO_80233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9539040975421) ^ 4769520487710 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9539040975421) ^ 3179680325140 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9539040975421) ^ 1907808195084 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9539040975421) ^ 867185543220 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9539040975421) ^ 502054788180 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9539040975421) ^ 19116314580 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9539040975421) ^ 118891740 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_12481064819203 : Nat.Prime 12481064819203 := by
  apply lucas_primality 12481064819203 (2 : ZMod 12481064819203)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (73, 1), (367, 1), (463, 1), (23957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (73, 1), (367, 1), (463, 1), (23957, 1)] : List FactorBlock).map factorBlockValue).prod) = 12481064819203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_73
      · exact prime_oneHundredFortySevenEO_367
      · exact prime_oneHundredFortySevenEO_463
      · exact prime_oneHundredFortySevenEO_23957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12481064819203) ^ 6240532409601 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12481064819203) ^ 4160354939734 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12481064819203) ^ 1783009259886 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12481064819203) ^ 170973490674 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12481064819203) ^ 34008351006 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12481064819203) ^ 26956943454 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12481064819203) ^ 520977786 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_16601083582793 : Nat.Prime 16601083582793 := by
  apply lucas_primality 16601083582793 (3 : ZMod 16601083582793)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (557, 1), (7079, 1), (526283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (557, 1), (7079, 1), (526283, 1)] : List FactorBlock).map factorBlockValue).prod) = 16601083582793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_557
      · exact prime_oneHundredFortySevenEO_7079
      · exact prime_oneHundredFortySevenEO_526283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16601083582793) ^ 8300541791396 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16601083582793) ^ 29804458856 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16601083582793) ^ 2345117048 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16601083582793) ^ 31544024 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_21386313733639 : Nat.Prime 21386313733639 := by
  apply lucas_primality 21386313733639 (3 : ZMod 21386313733639)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (5443, 1), (93550973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (5443, 1), (93550973, 1)] : List FactorBlock).map factorBlockValue).prod) = 21386313733639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_5443
      · exact prime_oneHundredFortySevenEO_93550973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21386313733639) ^ 10693156866819 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 21386313733639) ^ 7128771244546 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 21386313733639) ^ 3055187676234 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 21386313733639) ^ 3929140866 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 21386313733639) ^ 228606 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_38163848589571 : Nat.Prime 38163848589571 := by
  apply lucas_primality 38163848589571 (11 : ZMod 38163848589571)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (131, 1), (882809359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (131, 1), (882809359, 1)] : List FactorBlock).map factorBlockValue).prod) = 38163848589571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_131
      · exact prime_oneHundredFortySevenEO_882809359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 38163848589571) ^ 19081924294785 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 38163848589571) ^ 12721282863190 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 38163848589571) ^ 7632769717914 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 38163848589571) ^ 3469440780870 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 38163848589571) ^ 291327088470 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 38163848589571) ^ 43230 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_40043477642299 : Nat.Prime 40043477642299 := by
  apply lucas_primality 40043477642299 (2 : ZMod 40043477642299)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (89, 1), (12343, 1), (467333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (89, 1), (12343, 1), (467333, 1)] : List FactorBlock).map factorBlockValue).prod) = 40043477642299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_89
      · exact prime_oneHundredFortySevenEO_12343
      · exact prime_oneHundredFortySevenEO_467333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40043477642299) ^ 20021738821149 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 40043477642299) ^ 13347825880766 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 40043477642299) ^ 3080267510946 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 40043477642299) ^ 449926715082 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 40043477642299) ^ 3244225686 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 40043477642299) ^ 85685106 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_47
      · exact prime_oneHundredFortySevenEO_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_46289120187707 : Nat.Prime 46289120187707 := by
  apply lucas_primality 46289120187707 (2 : ZMod 46289120187707)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (587, 1), (3584413829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (587, 1), (3584413829, 1)] : List FactorBlock).map factorBlockValue).prod) = 46289120187707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_587
      · exact prime_oneHundredFortySevenEO_3584413829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46289120187707) ^ 23144560093853 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 46289120187707) ^ 4208101835246 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 46289120187707) ^ 78857104238 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 46289120187707) ^ 12914 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_54534374054357 : Nat.Prime 54534374054357 := by
  apply lucas_primality 54534374054357 (2 : ZMod 54534374054357)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (7019, 1), (15767, 1), (17599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (7019, 1), (15767, 1), (17599, 1)] : List FactorBlock).map factorBlockValue).prod) = 54534374054357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_7019
      · exact prime_oneHundredFortySevenEO_15767
      · exact prime_oneHundredFortySevenEO_17599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54534374054357) ^ 27267187027178 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 54534374054357) ^ 7790624864908 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 54534374054357) ^ 7769536124 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 54534374054357) ^ 3458766668 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 54534374054357) ^ 3098720044 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_73232680766393 : Nat.Prime 73232680766393 := by
  apply lucas_primality 73232680766393 (3 : ZMod 73232680766393)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (101, 1), (107, 1), (251, 1), (482101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (101, 1), (107, 1), (251, 1), (482101, 1)] : List FactorBlock).map factorBlockValue).prod) = 73232680766393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_101
      · exact prime_oneHundredFortySevenEO_107
      · exact prime_oneHundredFortySevenEO_251
      · exact prime_oneHundredFortySevenEO_482101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 73232680766393) ^ 36616340383196 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 73232680766393) ^ 10461811538056 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 73232680766393) ^ 725076047192 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 73232680766393) ^ 684417577256 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 73232680766393) ^ 291763668392 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 73232680766393) ^ 151903192 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_75455454880151 : Nat.Prime 75455454880151 := by
  apply lucas_primality 75455454880151 (11 : ZMod 75455454880151)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (863, 1), (1748677981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (863, 1), (1748677981, 1)] : List FactorBlock).map factorBlockValue).prod) = 75455454880151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_863
      · exact prime_oneHundredFortySevenEO_1748677981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 75455454880151) ^ 37727727440075 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 75455454880151) ^ 15091090976030 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 75455454880151) ^ 87433899050 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 75455454880151) ^ 43150 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_85817476640081 : Nat.Prime 85817476640081 := by
  apply lucas_primality 85817476640081 (3 : ZMod 85817476640081)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (82561, 1), (12993041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (82561, 1), (12993041, 1)] : List FactorBlock).map factorBlockValue).prod) = 85817476640081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_82561
      · exact prime_oneHundredFortySevenEO_12993041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 85817476640081) ^ 42908738320040 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85817476640081) ^ 17163495328016 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85817476640081) ^ 1039443280 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85817476640081) ^ 6604880 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_87027634159153 : Nat.Prime 87027634159153 := by
  apply lucas_primality 87027634159153 (5 : ZMod 87027634159153)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (521, 1), (112257799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (521, 1), (112257799, 1)] : List FactorBlock).map factorBlockValue).prod) = 87027634159153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_521
      · exact prime_oneHundredFortySevenEO_112257799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 87027634159153) ^ 43513817079576 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 87027634159153) ^ 29009211386384 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 87027634159153) ^ 2807343037392 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 87027634159153) ^ 167039604912 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 87027634159153) ^ 775248 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_109950250866671 : Nat.Prime 109950250866671 := by
  apply lucas_primality 109950250866671 (23 : ZMod 109950250866671)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1669, 1), (6587792143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1669, 1), (6587792143, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950250866671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_1669
      · exact prime_oneHundredFortySevenEO_6587792143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 109950250866671) ^ 54975125433335 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 109950250866671) ^ 21990050173334 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 109950250866671) ^ 65877921430 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (23 : ZMod 109950250866671) ^ 16690 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_139892943057233 : Nat.Prime 139892943057233 := by
  apply lucas_primality 139892943057233 (3 : ZMod 139892943057233)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (757, 1), (1663, 1), (2579, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (757, 1), (1663, 1), (2579, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) = 139892943057233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_757
      · exact prime_oneHundredFortySevenEO_1663
      · exact prime_oneHundredFortySevenEO_2579
      · exact prime_oneHundredFortySevenEO_2693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 139892943057233) ^ 69946471528616 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 139892943057233) ^ 184799132176 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 139892943057233) ^ 84120831664 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 139892943057233) ^ 54243095408 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 139892943057233) ^ 51946878224 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_181331007977881 : Nat.Prime 181331007977881 := by
  apply lucas_primality 181331007977881 (14 : ZMod 181331007977881)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (55966360487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (55966360487, 1)] : List FactorBlock).map factorBlockValue).prod) = 181331007977881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_55966360487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 181331007977881) ^ 90665503988940 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (14 : ZMod 181331007977881) ^ 60443669325960 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (14 : ZMod 181331007977881) ^ 36266201595576 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (14 : ZMod 181331007977881) ^ 3240 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_204285462728549 : Nat.Prime 204285462728549 := by
  apply lucas_primality 204285462728549 (2 : ZMod 204285462728549)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (46381, 1), (1101126877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (46381, 1), (1101126877, 1)] : List FactorBlock).map factorBlockValue).prod) = 204285462728549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_46381
      · exact prime_oneHundredFortySevenEO_1101126877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 204285462728549) ^ 102142731364274 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 204285462728549) ^ 4404507508 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 204285462728549) ^ 185524 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_247384381561903 : Nat.Prime 247384381561903 := by
  apply lucas_primality 247384381561903 (6 : ZMod 247384381561903)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1057198211803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1057198211803, 1)] : List FactorBlock).map factorBlockValue).prod) = 247384381561903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_1057198211803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 247384381561903) ^ 123692190780951 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 247384381561903) ^ 82461460520634 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 247384381561903) ^ 19029567812454 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 247384381561903) ^ 234 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_302970917474033 : Nat.Prime 302970917474033 := by
  apply lucas_primality 302970917474033 (3 : ZMod 302970917474033)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (277, 1), (3613, 1), (3617, 1), (5231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (277, 1), (3613, 1), (3617, 1), (5231, 1)] : List FactorBlock).map factorBlockValue).prod) = 302970917474033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_277
      · exact prime_oneHundredFortySevenEO_3613
      · exact prime_oneHundredFortySevenEO_3617
      · exact prime_oneHundredFortySevenEO_5231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 302970917474033) ^ 151485458737016 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 302970917474033) ^ 1093757824816 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 302970917474033) ^ 83855775664 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 302970917474033) ^ 83763040496 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 302970917474033) ^ 57918355472 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_348983269148419 : Nat.Prime 348983269148419 := by
  apply lucas_primality 348983269148419 (2 : ZMod 348983269148419)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (243363507077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (243363507077, 1)] : List FactorBlock).map factorBlockValue).prod) = 348983269148419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_239
      · exact prime_oneHundredFortySevenEO_243363507077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 348983269148419) ^ 174491634574209 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 348983269148419) ^ 116327756382806 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 348983269148419) ^ 1460181042462 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 348983269148419) ^ 1434 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_427889917416827 : Nat.Prime 427889917416827 := by
  apply lucas_primality 427889917416827 (2 : ZMod 427889917416827)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (24181, 1), (166936741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (24181, 1), (166936741, 1)] : List FactorBlock).map factorBlockValue).prod) = 427889917416827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_53
      · exact prime_oneHundredFortySevenEO_24181
      · exact prime_oneHundredFortySevenEO_166936741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 427889917416827) ^ 213944958708413 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 427889917416827) ^ 8073394668242 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 427889917416827) ^ 17695294546 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 427889917416827) ^ 2563186 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_511548911305717 : Nat.Prime 511548911305717 := by
  apply lucas_primality 511548911305717 (2 : ZMod 511548911305717)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (23, 1), (193, 1), (33229433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (23, 1), (193, 1), (33229433, 1)] : List FactorBlock).map factorBlockValue).prod) = 511548911305717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_193
      · exact prime_oneHundredFortySevenEO_33229433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 511548911305717) ^ 255774455652858 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 511548911305717) ^ 170516303768572 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 511548911305717) ^ 30091112429748 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 511548911305717) ^ 22241257013292 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 511548911305717) ^ 2650512493812 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 511548911305717) ^ 15394452 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_512864299805801 : Nat.Prime 512864299805801 := by
  apply lucas_primality 512864299805801 (3 : ZMod 512864299805801)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (4513, 1), (14323, 1), (39671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (4513, 1), (14323, 1), (39671, 1)] : List FactorBlock).map factorBlockValue).prod) = 512864299805801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_4513
      · exact prime_oneHundredFortySevenEO_14323
      · exact prime_oneHundredFortySevenEO_39671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 512864299805801) ^ 256432149902900 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 512864299805801) ^ 102572859961160 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 512864299805801) ^ 113641546600 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 512864299805801) ^ 35807044600 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 512864299805801) ^ 12927939800 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_544972419305527 : Nat.Prime 544972419305527 := by
  apply lucas_primality 544972419305527 (3 : ZMod 544972419305527)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (653, 1), (1483, 1), (93792679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (653, 1), (1483, 1), (93792679, 1)] : List FactorBlock).map factorBlockValue).prod) = 544972419305527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_653
      · exact prime_oneHundredFortySevenEO_1483
      · exact prime_oneHundredFortySevenEO_93792679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 544972419305527) ^ 272486209652763 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 544972419305527) ^ 181657473101842 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 544972419305527) ^ 834567257742 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 544972419305527) ^ 367479716322 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 544972419305527) ^ 5810394 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_701
      · exact prime_oneHundredFortySevenEO_9769
      · exact prime_oneHundredFortySevenEO_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_621760403722501 : Nat.Prime 621760403722501 := by
  apply lucas_primality 621760403722501 (26 : ZMod 621760403722501)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 4), (7, 1), (59, 1), (66909917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 4), (7, 1), (59, 1), (66909917, 1)] : List FactorBlock).map factorBlockValue).prod) = 621760403722501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_59
      · exact prime_oneHundredFortySevenEO_66909917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 621760403722501) ^ 310880201861250 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 207253467907500 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 124352080744500 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 88822914817500 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 10538311927500 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 9292500 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1031841622157627 : Nat.Prime 1031841622157627 := by
  apply lucas_primality 1031841622157627 (2 : ZMod 1031841622157627)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1625759, 1), (45334501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1625759, 1), (45334501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1031841622157627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_1625759
      · exact prime_oneHundredFortySevenEO_45334501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1031841622157627) ^ 515920811078813 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1031841622157627) ^ 147405946022518 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1031841622157627) ^ 634683014 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1031841622157627) ^ 22760626 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1162164053665001 : Nat.Prime 1162164053665001 := by
  apply lucas_primality 1162164053665001 (3 : ZMod 1162164053665001)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 4), (443, 1), (524679031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 4), (443, 1), (524679031, 1)] : List FactorBlock).map factorBlockValue).prod) = 1162164053665001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_443
      · exact prime_oneHundredFortySevenEO_524679031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1162164053665001) ^ 581082026832500 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1162164053665001) ^ 232432810733000 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1162164053665001) ^ 2623395155000 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1162164053665001) ^ 2215000 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1188741935720723 : Nat.Prime 1188741935720723 := by
  apply lucas_primality 1188741935720723 (2 : ZMod 1188741935720723)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1471, 1), (23768183623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1471, 1), (23768183623, 1)] : List FactorBlock).map factorBlockValue).prod) = 1188741935720723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_1471
      · exact prime_oneHundredFortySevenEO_23768183623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1188741935720723) ^ 594370967860361 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188741935720723) ^ 69925996218866 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188741935720723) ^ 808118243182 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188741935720723) ^ 50014 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2155831346712731 : Nat.Prime 2155831346712731 := by
  apply lucas_primality 2155831346712731 (2 : ZMod 2155831346712731)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1069, 1), (1847, 1), (1879, 1), (58109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1069, 1), (1847, 1), (1879, 1), (58109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2155831346712731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_1069
      · exact prime_oneHundredFortySevenEO_1847
      · exact prime_oneHundredFortySevenEO_1879
      · exact prime_oneHundredFortySevenEO_58109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2155831346712731) ^ 1077915673356365 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2155831346712731) ^ 431166269342546 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2155831346712731) ^ 2016680399170 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2155831346712731) ^ 1167207009590 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2155831346712731) ^ 1147329082870 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2155831346712731) ^ 37099783970 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2219515269182291 : Nat.Prime 2219515269182291 := by
  apply lucas_primality 2219515269182291 (2 : ZMod 2219515269182291)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (2467, 1), (2092283509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (2467, 1), (2092283509, 1)] : List FactorBlock).map factorBlockValue).prod) = 2219515269182291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_43
      · exact prime_oneHundredFortySevenEO_2467
      · exact prime_oneHundredFortySevenEO_2092283509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2219515269182291) ^ 1109757634591145 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2219515269182291) ^ 443903053836458 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2219515269182291) ^ 51616634167030 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2219515269182291) ^ 899681908870 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2219515269182291) ^ 1060810 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2324328107330003 : Nat.Prime 2324328107330003 := by
  apply lucas_primality 2324328107330003 (2 : ZMod 2324328107330003)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1162164053665001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1162164053665001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2324328107330003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_1162164053665001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2324328107330003) ^ 1162164053665001 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2324328107330003) ^ 2 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2551726861020299 : Nat.Prime 2551726861020299 := by
  apply lucas_primality 2551726861020299 (2 : ZMod 2551726861020299)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (269, 1), (364845133117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (269, 1), (364845133117, 1)] : List FactorBlock).map factorBlockValue).prod) = 2551726861020299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_269
      · exact prime_oneHundredFortySevenEO_364845133117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2551726861020299) ^ 1275863430510149 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2551726861020299) ^ 196286681616946 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2551726861020299) ^ 9485973461042 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2551726861020299) ^ 6994 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2653652154361081 : Nat.Prime 2653652154361081 := by
  apply lucas_primality 2653652154361081 (7 : ZMod 2653652154361081)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (241, 1), (607, 1), (151167007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (241, 1), (607, 1), (151167007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2653652154361081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_241
      · exact prime_oneHundredFortySevenEO_607
      · exact prime_oneHundredFortySevenEO_151167007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2653652154361081) ^ 1326826077180540 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2653652154361081) ^ 884550718120360 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2653652154361081) ^ 530730430872216 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2653652154361081) ^ 11011004789880 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2653652154361081) ^ 4371749842440 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2653652154361081) ^ 17554440 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2900303382201587 : Nat.Prime 2900303382201587 := by
  apply lucas_primality 2900303382201587 (2 : ZMod 2900303382201587)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 2), (1509002800313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 2), (1509002800313, 1)] : List FactorBlock).map factorBlockValue).prod) = 2900303382201587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_1509002800313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2900303382201587) ^ 1450151691100793 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2900303382201587) ^ 93558173619406 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2900303382201587) ^ 1922 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3496155830694049 : Nat.Prime 3496155830694049 := by
  apply lucas_primality 3496155830694049 (7 : ZMod 3496155830694049)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (137, 1), (643, 1), (24318629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (137, 1), (643, 1), (24318629, 1)] : List FactorBlock).map factorBlockValue).prod) = 3496155830694049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_137
      · exact prime_oneHundredFortySevenEO_643
      · exact prime_oneHundredFortySevenEO_24318629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3496155830694049) ^ 1748077915347024 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3496155830694049) ^ 1165385276898016 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3496155830694049) ^ 205656225334944 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3496155830694049) ^ 25519385625504 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3496155830694049) ^ 5437256346336 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3496155830694049) ^ 143764512 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3824445099696161 : Nat.Prime 3824445099696161 := by
  apply lucas_primality 3824445099696161 (3 : ZMod 3824445099696161)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (23, 1), (1039251385787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (23, 1), (1039251385787, 1)] : List FactorBlock).map factorBlockValue).prod) = 3824445099696161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_1039251385787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3824445099696161) ^ 1912222549848080 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3824445099696161) ^ 764889019939232 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3824445099696161) ^ 166280221725920 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3824445099696161) ^ 3680 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4122049274682037 : Nat.Prime 4122049274682037 := by
  apply lucas_primality 4122049274682037 (6 : ZMod 4122049274682037)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (61, 1), (229, 1), (271, 1), (2927087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (61, 1), (229, 1), (271, 1), (2927087, 1)] : List FactorBlock).map factorBlockValue).prod) = 4122049274682037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_229
      · exact prime_oneHundredFortySevenEO_271
      · exact prime_oneHundredFortySevenEO_2927087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4122049274682037) ^ 2061024637341018 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4122049274682037) ^ 1374016424894012 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4122049274682037) ^ 132969331441356 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4122049274682037) ^ 67574578273476 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4122049274682037) ^ 18000215173284 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4122049274682037) ^ 15210513928716 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 4122049274682037) ^ 1408242828 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4311662693425463 : Nat.Prime 4311662693425463 := by
  apply lucas_primality 4311662693425463 (5 : ZMod 4311662693425463)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2155831346712731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2155831346712731, 1)] : List FactorBlock).map factorBlockValue).prod) = 4311662693425463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_2155831346712731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4311662693425463) ^ 2155831346712731 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4311662693425463) ^ 2 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6217604037225011 : Nat.Prime 6217604037225011 := by
  apply lucas_primality 6217604037225011 (2 : ZMod 6217604037225011)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (621760403722501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (621760403722501, 1)] : List FactorBlock).map factorBlockValue).prod) = 6217604037225011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_621760403722501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6217604037225011) ^ 3108802018612505 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6217604037225011) ^ 1243520807445002 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6217604037225011) ^ 10 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6771271330445161 : Nat.Prime 6771271330445161 := by
  apply lucas_primality 6771271330445161 (29 : ZMod 6771271330445161)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1), (83, 1), (1217, 1), (426757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (17, 1), (83, 1), (1217, 1), (426757, 1)] : List FactorBlock).map factorBlockValue).prod) = 6771271330445161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_83
      · exact prime_oneHundredFortySevenEO_1217
      · exact prime_oneHundredFortySevenEO_426757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 6771271330445161) ^ 3385635665222580 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 6771271330445161) ^ 2257090443481720 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 6771271330445161) ^ 1354254266089032 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 6771271330445161) ^ 967324475777880 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 6771271330445161) ^ 615570120949560 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 6771271330445161) ^ 398310078261480 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 6771271330445161) ^ 81581582294520 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 6771271330445161) ^ 5563904133480 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 6771271330445161) ^ 15866807880 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_7968064225615061 : Nat.Prime 7968064225615061 := by
  apply lucas_primality 7968064225615061 (2 : ZMod 7968064225615061)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (79, 1), (720439803401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (79, 1), (720439803401, 1)] : List FactorBlock).map factorBlockValue).prod) = 7968064225615061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_79
      · exact prime_oneHundredFortySevenEO_720439803401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7968064225615061) ^ 3984032112807530 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7968064225615061) ^ 1593612845123012 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7968064225615061) ^ 1138294889373580 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7968064225615061) ^ 100861572476140 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7968064225615061) ^ 11060 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_8926185979551947 : Nat.Prime 8926185979551947 := by
  apply lucas_primality 8926185979551947 (2 : ZMod 8926185979551947)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (45361, 1), (484682431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (45361, 1), (484682431, 1)] : List FactorBlock).map factorBlockValue).prod) = 8926185979551947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_29
      · exact prime_oneHundredFortySevenEO_45361
      · exact prime_oneHundredFortySevenEO_484682431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8926185979551947) ^ 4463092989775973 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8926185979551947) ^ 1275169425650278 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8926185979551947) ^ 307799516536274 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8926185979551947) ^ 196781066986 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8926185979551947) ^ 18416566 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_11487647709008197 : Nat.Prime 11487647709008197 := by
  apply lucas_primality 11487647709008197 (2 : ZMod 11487647709008197)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (87027634159153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (87027634159153, 1)] : List FactorBlock).map factorBlockValue).prod) = 11487647709008197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_87027634159153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11487647709008197) ^ 5743823854504098 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11487647709008197) ^ 3829215903002732 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11487647709008197) ^ 1044331609909836 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11487647709008197) ^ 132 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_14269080191837767 : Nat.Prime 14269080191837767 := by
  apply lucas_primality 14269080191837767 (3 : ZMod 14269080191837767)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (139892943057233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (139892943057233, 1)] : List FactorBlock).map factorBlockValue).prod) = 14269080191837767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_139892943057233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14269080191837767) ^ 7134540095918883 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 14269080191837767) ^ 4756360063945922 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 14269080191837767) ^ 839357658343398 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 14269080191837767) ^ 102 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_18104479039497973 : Nat.Prime 18104479039497973 := by
  apply lucas_primality 18104479039497973 (7 : ZMod 18104479039497973)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (37, 2), (89, 1), (9733, 1), (115657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (37, 2), (89, 1), (9733, 1), (115657, 1)] : List FactorBlock).map factorBlockValue).prod) = 18104479039497973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_37
      · exact prime_oneHundredFortySevenEO_89
      · exact prime_oneHundredFortySevenEO_9733
      · exact prime_oneHundredFortySevenEO_115657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18104479039497973) ^ 9052239519748986 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 18104479039497973) ^ 6034826346499324 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 18104479039497973) ^ 1645861730863452 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 18104479039497973) ^ 489310244310756 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 18104479039497973) ^ 203421112803348 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 18104479039497973) ^ 1860112918884 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 18104479039497973) ^ 156535955796 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_21819548052590423 : Nat.Prime 21819548052590423 := by
  apply lucas_primality 21819548052590423 (5 : ZMod 21819548052590423)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (338231, 1), (1897376093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (338231, 1), (1897376093, 1)] : List FactorBlock).map factorBlockValue).prod) = 21819548052590423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_338231
      · exact prime_oneHundredFortySevenEO_1897376093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21819548052590423) ^ 10909774026295211 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 21819548052590423) ^ 1283502826622966 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 21819548052590423) ^ 64510787162 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 21819548052590423) ^ 11499854 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_25399657881673291 : Nat.Prime 25399657881673291 := by
  apply lucas_primality 25399657881673291 (3 : ZMod 25399657881673291)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (16601083582793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (16601083582793, 1)] : List FactorBlock).map factorBlockValue).prod) = 25399657881673291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_16601083582793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25399657881673291) ^ 12699828940836645 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25399657881673291) ^ 8466552627224430 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25399657881673291) ^ 5079931576334658 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25399657881673291) ^ 1494097522451370 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 25399657881673291) ^ 1530 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_35590725838477547 : Nat.Prime 35590725838477547 := by
  apply lucas_primality 35590725838477547 (2 : ZMod 35590725838477547)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (23, 1), (41, 1), (1069, 1), (94400837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (23, 1), (41, 1), (1069, 1), (94400837, 1)] : List FactorBlock).map factorBlockValue).prod) = 35590725838477547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_41
      · exact prime_oneHundredFortySevenEO_1069
      · exact prime_oneHundredFortySevenEO_94400837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35590725838477547) ^ 17795362919238773 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35590725838477547) ^ 3235520530770686 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35590725838477547) ^ 2093572108145738 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35590725838477547) ^ 1547422862542502 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35590725838477547) ^ 868066483865306 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35590725838477547) ^ 33293475994834 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35590725838477547) ^ 377017058 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_145829
      · exact prime_oneHundredFortySevenEO_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_55837323063747041 : Nat.Prime 55837323063747041 := by
  apply lucas_primality 55837323063747041 (3 : ZMod 55837323063747041)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (348983269148419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (348983269148419, 1)] : List FactorBlock).map factorBlockValue).prod) = 55837323063747041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_348983269148419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55837323063747041) ^ 27918661531873520 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 55837323063747041) ^ 11167464612749408 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 55837323063747041) ^ 160 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_61765933691376437 : Nat.Prime 61765933691376437 := by
  apply lucas_primality 61765933691376437 (2 : ZMod 61765933691376437)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (263, 1), (39079, 1), (65322379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (263, 1), (39079, 1), (65322379, 1)] : List FactorBlock).map factorBlockValue).prod) = 61765933691376437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_263
      · exact prime_oneHundredFortySevenEO_39079
      · exact prime_oneHundredFortySevenEO_65322379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61765933691376437) ^ 30882966845688218 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61765933691376437) ^ 2685475377885932 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61765933691376437) ^ 234851458902572 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61765933691376437) ^ 1580540282284 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61765933691376437) ^ 945555484 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_68626231460786887 : Nat.Prime 68626231460786887 := by
  apply lucas_primality 68626231460786887 (3 : ZMod 68626231460786887)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (4243, 1), (23855439659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (4243, 1), (23855439659, 1)] : List FactorBlock).map factorBlockValue).prod) = 68626231460786887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_113
      · exact prime_oneHundredFortySevenEO_4243
      · exact prime_oneHundredFortySevenEO_23855439659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68626231460786887) ^ 34313115730393443 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 68626231460786887) ^ 22875410486928962 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 68626231460786887) ^ 607311782838822 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 68626231460786887) ^ 16173988088802 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 68626231460786887) ^ 2876754 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_72417916157991893 : Nat.Prime 72417916157991893 := by
  apply lucas_primality 72417916157991893 (2 : ZMod 72417916157991893)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18104479039497973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18104479039497973, 1)] : List FactorBlock).map factorBlockValue).prod) = 72417916157991893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_18104479039497973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 72417916157991893) ^ 36208958078995946 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 72417916157991893) ^ 4 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_90281015094265453 : Nat.Prime 90281015094265453 := by
  apply lucas_primality 90281015094265453 (2 : ZMod 90281015094265453)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (47, 1), (53, 1), (1006746677977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (47, 1), (53, 1), (1006746677977, 1)] : List FactorBlock).map factorBlockValue).prod) = 90281015094265453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_47
      · exact prime_oneHundredFortySevenEO_53
      · exact prime_oneHundredFortySevenEO_1006746677977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90281015094265453) ^ 45140507547132726 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 90281015094265453) ^ 30093671698088484 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 90281015094265453) ^ 1920872661580116 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 90281015094265453) ^ 1703415379137084 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 90281015094265453) ^ 89676 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_90533246765019143 : Nat.Prime 90533246765019143 := by
  apply lucas_primality 90533246765019143 (5 : ZMod 90533246765019143)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (97, 1), (9523800417107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (97, 1), (9523800417107, 1)] : List FactorBlock).map factorBlockValue).prod) = 90533246765019143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_97
      · exact prime_oneHundredFortySevenEO_9523800417107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 90533246765019143) ^ 45266623382509571 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 90533246765019143) ^ 12933320966431306 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 90533246765019143) ^ 933332440876486 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 90533246765019143) ^ 9506 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_161745465501931879 : Nat.Prime 161745465501931879 := by
  apply lucas_primality 161745465501931879 (3 : ZMod 161745465501931879)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (38707, 1), (33164393279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (38707, 1), (33164393279, 1)] : List FactorBlock).map factorBlockValue).prod) = 161745465501931879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_38707
      · exact prime_oneHundredFortySevenEO_33164393279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 161745465501931879) ^ 80872732750965939 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 161745465501931879) ^ 53915155167310626 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 161745465501931879) ^ 23106495071704554 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 161745465501931879) ^ 4178713553154 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 161745465501931879) ^ 4877082 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_163955262580311479 : Nat.Prime 163955262580311479 := by
  apply lucas_primality 163955262580311479 (7 : ZMod 163955262580311479)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (761437, 1), (418917271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (761437, 1), (418917271, 1)] : List FactorBlock).map factorBlockValue).prod) = 163955262580311479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_257
      · exact prime_oneHundredFortySevenEO_761437
      · exact prime_oneHundredFortySevenEO_418917271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 163955262580311479) ^ 81977631290155739 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 163955262580311479) ^ 637958220156854 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 163955262580311479) ^ 215323477294 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 163955262580311479) ^ 391378618 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_231638049393583901 : Nat.Prime 231638049393583901 := by
  apply lucas_primality 231638049393583901 (2 : ZMod 231638049393583901)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (47, 1), (601, 1), (38561, 1), (2126617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (47, 1), (601, 1), (38561, 1), (2126617, 1)] : List FactorBlock).map factorBlockValue).prod) = 231638049393583901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_47
      · exact prime_oneHundredFortySevenEO_601
      · exact prime_oneHundredFortySevenEO_38561
      · exact prime_oneHundredFortySevenEO_2126617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 231638049393583901) ^ 115819024696791950 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 231638049393583901) ^ 46327609878716780 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 231638049393583901) ^ 4928469136033700 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 231638049393583901) ^ 385421047243900 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 231638049393583901) ^ 6007055039900 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 231638049393583901) ^ 108923256700 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_335902595973800657 : Nat.Prime 335902595973800657 := by
  apply lucas_primality 335902595973800657 (3 : ZMod 335902595973800657)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (53, 1), (1559, 1), (97453, 1), (113357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (53, 1), (1559, 1), (97453, 1), (113357, 1)] : List FactorBlock).map factorBlockValue).prod) = 335902595973800657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_53
      · exact prime_oneHundredFortySevenEO_1559
      · exact prime_oneHundredFortySevenEO_97453
      · exact prime_oneHundredFortySevenEO_113357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 335902595973800657) ^ 167951297986900328 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 14604460694513072 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 6337784829694352 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 215460292478384 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 3446816372752 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 2963227643408 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_403953554336384389 : Nat.Prime 403953554336384389 := by
  apply lucas_primality 403953554336384389 (11 : ZMod 403953554336384389)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 1), (24337, 1), (3728286137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 1), (24337, 1), (3728286137, 1)] : List FactorBlock).map factorBlockValue).prod) = 403953554336384389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_53
      · exact prime_oneHundredFortySevenEO_24337
      · exact prime_oneHundredFortySevenEO_3728286137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 403953554336384389) ^ 201976777168192194 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 403953554336384389) ^ 134651184778794796 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 403953554336384389) ^ 57707650619483484 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 403953554336384389) ^ 7621765176158196 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 403953554336384389) ^ 16598329881924 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 403953554336384389) ^ 108348324 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_912749576063961191 : Nat.Prime 912749576063961191 := by
  apply lucas_primality 912749576063961191 (29 : ZMod 912749576063961191)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12689, 1), (281933, 1), (25513987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12689, 1), (281933, 1), (25513987, 1)] : List FactorBlock).map factorBlockValue).prod) = 912749576063961191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_12689
      · exact prime_oneHundredFortySevenEO_281933
      · exact prime_oneHundredFortySevenEO_25513987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 912749576063961191) ^ 456374788031980595 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 912749576063961191) ^ 182549915212792238 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 912749576063961191) ^ 71932348968710 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 912749576063961191) ^ 3237469810430 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (29 : ZMod 912749576063961191) ^ 35774478370 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1311642100642491833 : Nat.Prime 1311642100642491833 := by
  apply lucas_primality 1311642100642491833 (3 : ZMod 1311642100642491833)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (163955262580311479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (163955262580311479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1311642100642491833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_163955262580311479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1311642100642491833) ^ 655821050321245916 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1311642100642491833) ^ 8 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1516066471040061133 : Nat.Prime 1516066471040061133 := by
  apply lucas_primality 1516066471040061133 (2 : ZMod 1516066471040061133)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (139, 1), (302970917474033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (139, 1), (302970917474033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1516066471040061133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_139
      · exact prime_oneHundredFortySevenEO_302970917474033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1516066471040061133) ^ 758033235520030566 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1516066471040061133) ^ 505355490346687044 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1516066471040061133) ^ 10906953029065188 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1516066471040061133) ^ 5004 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2255754474308703341 : Nat.Prime 2255754474308703341 := by
  apply lucas_primality 2255754474308703341 (3 : ZMod 2255754474308703341)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (79, 1), (58699, 1), (3474609461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (79, 1), (58699, 1), (3474609461, 1)] : List FactorBlock).map factorBlockValue).prod) = 2255754474308703341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_79
      · exact prime_oneHundredFortySevenEO_58699
      · exact prime_oneHundredFortySevenEO_3474609461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2255754474308703341) ^ 1127877237154351670 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255754474308703341) ^ 451150894861740668 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255754474308703341) ^ 322250639186957620 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255754474308703341) ^ 28553854105173460 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255754474308703341) ^ 38429180638660 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255754474308703341) ^ 649210940 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_2303060573119184687 : Nat.Prime 2303060573119184687 := by
  apply lucas_primality 2303060573119184687 (5 : ZMod 2303060573119184687)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (193, 1), (40043477642299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (193, 1), (40043477642299, 1)] : List FactorBlock).map factorBlockValue).prod) = 2303060573119184687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_149
      · exact prime_oneHundredFortySevenEO_193
      · exact prime_oneHundredFortySevenEO_40043477642299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2303060573119184687) ^ 1151530286559592343 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2303060573119184687) ^ 15456782369927414 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2303060573119184687) ^ 11932956337405102 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2303060573119184687) ^ 57514 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4094685267827061811 : Nat.Prime 4094685267827061811 := by
  apply lucas_primality 4094685267827061811 (3 : ZMod 4094685267827061811)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (87811, 1), (222050782651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (87811, 1), (222050782651, 1)] : List FactorBlock).map factorBlockValue).prod) = 4094685267827061811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_87811
      · exact prime_oneHundredFortySevenEO_222050782651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4094685267827061811) ^ 2047342633913530905 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4094685267827061811) ^ 1364895089275687270 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4094685267827061811) ^ 818937053565412362 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4094685267827061811) ^ 584955038261008830 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4094685267827061811) ^ 46630664356710 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4094685267827061811) ^ 18440310 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5800750756247764409 : Nat.Prime 5800750756247764409 := by
  apply lucas_primality 5800750756247764409 (3 : ZMod 5800750756247764409)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (7968064225615061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (7968064225615061, 1)] : List FactorBlock).map factorBlockValue).prod) = 5800750756247764409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_7968064225615061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5800750756247764409) ^ 2900375378123882204 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5800750756247764409) ^ 828678679463966344 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5800750756247764409) ^ 446211596634443416 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5800750756247764409) ^ 728 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6978129937577018323 : Nat.Prime 6978129937577018323 := by
  apply lucas_primality 6978129937577018323 (3 : ZMod 6978129937577018323)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (401, 1), (2900303382201587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (401, 1), (2900303382201587, 1)] : List FactorBlock).map factorBlockValue).prod) = 6978129937577018323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_401
      · exact prime_oneHundredFortySevenEO_2900303382201587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6978129937577018323) ^ 3489064968788509161 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6978129937577018323) ^ 2326043312525672774 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6978129937577018323) ^ 17401820293209522 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6978129937577018323) ^ 2406 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_8180544491420909269 : Nat.Prime 8180544491420909269 := by
  apply lucas_primality 8180544491420909269 (2 : ZMod 8180544491420909269)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (83, 1), (2393, 1), (201897644693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (83, 1), (2393, 1), (201897644693, 1)] : List FactorBlock).map factorBlockValue).prod) = 8180544491420909269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_83
      · exact prime_oneHundredFortySevenEO_2393
      · exact prime_oneHundredFortySevenEO_201897644693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8180544491420909269) ^ 4090272245710454634 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8180544491420909269) ^ 2726848163806969756 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8180544491420909269) ^ 481208499495347604 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8180544491420909269) ^ 98560777005071196 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8180544491420909269) ^ 3418530919941876 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8180544491420909269) ^ 40518276 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_10110882662367189709 : Nat.Prime 10110882662367189709 := by
  apply lucas_primality 10110882662367189709 (2 : ZMod 10110882662367189709)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (241, 1), (3496155830694049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (241, 1), (3496155830694049, 1)] : List FactorBlock).map factorBlockValue).prod) = 10110882662367189709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_241
      · exact prime_oneHundredFortySevenEO_3496155830694049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10110882662367189709) ^ 5055441331183594854 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10110882662367189709) ^ 3370294220789063236 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10110882662367189709) ^ 41953869968328588 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10110882662367189709) ^ 2892 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_13151161881056247751 : Nat.Prime 13151161881056247751 := by
  apply lucas_primality 13151161881056247751 (3 : ZMod 13151161881056247751)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (13, 2), (2909, 1), (11889160219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (13, 2), (2909, 1), (11889160219, 1)] : List FactorBlock).map factorBlockValue).prod) = 13151161881056247751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_2909
      · exact prime_oneHundredFortySevenEO_11889160219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13151161881056247751) ^ 6575580940528123875 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13151161881056247751) ^ 4383720627018749250 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13151161881056247751) ^ 2630232376211249550 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13151161881056247751) ^ 1011627837004326750 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13151161881056247751) ^ 4520853173274750 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13151161881056247751) ^ 1106147250 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_31840361531301202493 : Nat.Prime 31840361531301202493 := by
  apply lucas_primality 31840361531301202493 (2 : ZMod 31840361531301202493)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5651, 1), (27732071, 1), (50793763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5651, 1), (27732071, 1), (50793763, 1)] : List FactorBlock).map factorBlockValue).prod) = 31840361531301202493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5651
      · exact prime_oneHundredFortySevenEO_27732071
      · exact prime_oneHundredFortySevenEO_50793763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31840361531301202493) ^ 15920180765650601246 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31840361531301202493) ^ 5634464967492692 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31840361531301202493) ^ 1148142218852 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31840361531301202493) ^ 626855732884 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_76364612785197585103 : Nat.Prime 76364612785197585103 := by
  apply lucas_primality 76364612785197585103 (5 : ZMod 76364612785197585103)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (6217604037225011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (6217604037225011, 1)] : List FactorBlock).map factorBlockValue).prod) = 76364612785197585103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_89
      · exact prime_oneHundredFortySevenEO_6217604037225011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76364612785197585103) ^ 38182306392598792551 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 25454870928399195034 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 3320200555878155874 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 858029357137051518 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 12282 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_87910768541306777201 : Nat.Prime 87910768541306777201 := by
  apply lucas_primality 87910768541306777201 (3 : ZMod 87910768541306777201)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (37, 1), (227, 1), (1648349, 1), (15874693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (37, 1), (227, 1), (1648349, 1), (15874693, 1)] : List FactorBlock).map factorBlockValue).prod) = 87910768541306777201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_37
      · exact prime_oneHundredFortySevenEO_227
      · exact prime_oneHundredFortySevenEO_1648349
      · exact prime_oneHundredFortySevenEO_15874693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87910768541306777201) ^ 43955384270653388600 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 87910768541306777201) ^ 17582153708261355440 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 87910768541306777201) ^ 2375966717332615600 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 87910768541306777201) ^ 387272108111483600 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 87910768541306777201) ^ 53332618602800 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 87910768541306777201) ^ 5537793300400 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_113265254864242715791 : Nat.Prime 113265254864242715791 := by
  apply lucas_primality 113265254864242715791 (6 : ZMod 113265254864242715791)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3659, 1), (1031841622157627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3659, 1), (1031841622157627, 1)] : List FactorBlock).map factorBlockValue).prod) = 113265254864242715791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_3659
      · exact prime_oneHundredFortySevenEO_1031841622157627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 113265254864242715791) ^ 56632627432121357895 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 113265254864242715791) ^ 37755084954747571930 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 113265254864242715791) ^ 22653050972848543158 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 113265254864242715791) ^ 30955248664728810 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 113265254864242715791) ^ 109770 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_183924083133023137391 : Nat.Prime 183924083133023137391 := by
  apply lucas_primality 183924083133023137391 (11 : ZMod 183924083133023137391)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (193, 1), (2324328107330003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (193, 1), (2324328107330003, 1)] : List FactorBlock).map factorBlockValue).prod) = 183924083133023137391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_41
      · exact prime_oneHundredFortySevenEO_193
      · exact prime_oneHundredFortySevenEO_2324328107330003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 183924083133023137391) ^ 91962041566511568695 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 183924083133023137391) ^ 36784816626604627478 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 183924083133023137391) ^ 4485953247146905790 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 183924083133023137391) ^ 952974524005301230 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (11 : ZMod 183924083133023137391) ^ 79130 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_208736198681259388691 : Nat.Prime 208736198681259388691 := by
  apply lucas_primality 208736198681259388691 (6 : ZMod 208736198681259388691)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1672423, 1), (12481064819203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1672423, 1), (12481064819203, 1)] : List FactorBlock).map factorBlockValue).prod) = 208736198681259388691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_1672423
      · exact prime_oneHundredFortySevenEO_12481064819203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 208736198681259388691) ^ 104368099340629694345 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 208736198681259388691) ^ 41747239736251877738 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 208736198681259388691) ^ 124810648192030 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 208736198681259388691) ^ 16724230 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_73
      · exact prime_oneHundredFortySevenEO_79
      · exact prime_oneHundredFortySevenEO_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_6863
      · exact prime_oneHundredFortySevenEO_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_292518227394514319039 : Nat.Prime 292518227394514319039 := by
  apply lucas_primality 292518227394514319039 (7 : ZMod 292518227394514319039)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (128568031, 1), (1137600946049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (128568031, 1), (1137600946049, 1)] : List FactorBlock).map factorBlockValue).prod) = 292518227394514319039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_128568031
      · exact prime_oneHundredFortySevenEO_1137600946049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 292518227394514319039) ^ 146259113697257159519 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 292518227394514319039) ^ 2275201892098 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 292518227394514319039) ^ 257136062 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_361609103000024689093 : Nat.Prime 361609103000024689093 := by
  apply lucas_primality 361609103000024689093 (2 : ZMod 361609103000024689093)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (180926927, 1), (166553936533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (180926927, 1), (166553936533, 1)] : List FactorBlock).map factorBlockValue).prod) = 361609103000024689093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_180926927
      · exact prime_oneHundredFortySevenEO_166553936533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361609103000024689093) ^ 180804551500012344546 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 361609103000024689093) ^ 120536367666674896364 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 361609103000024689093) ^ 1998647238396 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 361609103000024689093) ^ 2171123124 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_548456159849912872529 : Nat.Prime 548456159849912872529 := by
  apply lucas_primality 548456159849912872529 (3 : ZMod 548456159849912872529)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1571, 1), (21819548052590423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1571, 1), (21819548052590423, 1)] : List FactorBlock).map factorBlockValue).prod) = 548456159849912872529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_1571
      · exact prime_oneHundredFortySevenEO_21819548052590423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 548456159849912872529) ^ 274228079924956436264 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 548456159849912872529) ^ 349112768841446768 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 548456159849912872529) ^ 25136 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_575284891189512700303 : Nat.Prime 575284891189512700303 := by
  apply lucas_primality 575284891189512700303 (5 : ZMod 575284891189512700303)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1709, 1), (12823, 1), (4375221181031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1709, 1), (12823, 1), (4375221181031, 1)] : List FactorBlock).map factorBlockValue).prod) = 575284891189512700303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_1709
      · exact prime_oneHundredFortySevenEO_12823
      · exact prime_oneHundredFortySevenEO_4375221181031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 575284891189512700303) ^ 287642445594756350151 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 191761630396504233434 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 336620767226163078 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 44863517990291874 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 131487042 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_618888851413845735299 : Nat.Prime 618888851413845735299 := by
  apply lucas_primality 618888851413845735299 (2 : ZMod 618888851413845735299)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (3671, 1), (427889917416827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (3671, 1), (427889917416827, 1)] : List FactorBlock).map factorBlockValue).prod) = 618888851413845735299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_197
      · exact prime_oneHundredFortySevenEO_3671
      · exact prime_oneHundredFortySevenEO_427889917416827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 618888851413845735299) ^ 309444425706922867649 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 618888851413845735299) ^ 3141567773674343834 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 618888851413845735299) ^ 168588627462229838 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 618888851413845735299) ^ 1446374 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_817854625343146538137 : Nat.Prime 817854625343146538137 := by
  apply lucas_primality 817854625343146538137 (15 : ZMod 817854625343146538137)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (56807, 1), (54534374054357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (56807, 1), (54534374054357, 1)] : List FactorBlock).map factorBlockValue).prod) = 817854625343146538137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_56807
      · exact prime_oneHundredFortySevenEO_54534374054357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 817854625343146538137) ^ 408927312671573269068 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (15 : ZMod 817854625343146538137) ^ 272618208447715512712 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (15 : ZMod 817854625343146538137) ^ 74350420485740594376 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (15 : ZMod 817854625343146538137) ^ 14397074750350248 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (15 : ZMod 817854625343146538137) ^ 14997048 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_1549
      · exact prime_oneHundredFortySevenEO_47713
      · exact prime_oneHundredFortySevenEO_341461
      · exact prime_oneHundredFortySevenEO_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3966390446257410754147 : Nat.Prime 3966390446257410754147 := by
  apply lucas_primality 3966390446257410754147 (3 : ZMod 3966390446257410754147)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (194819, 1), (5760996460301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (194819, 1), (5760996460301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3966390446257410754147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_31
      · exact prime_oneHundredFortySevenEO_194819
      · exact prime_oneHundredFortySevenEO_5760996460301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3966390446257410754147) ^ 1983195223128705377073 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3966390446257410754147) ^ 1322130148752470251382 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3966390446257410754147) ^ 208757391908284776534 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3966390446257410754147) ^ 127948078911529379166 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3966390446257410754147) ^ 20359361490703734 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3966390446257410754147) ^ 688490346 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3970959864830274425357 : Nat.Prime 3970959864830274425357 := by
  apply lucas_primality 3970959864830274425357 (2 : ZMod 3970959864830274425357)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (76364612785197585103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (76364612785197585103, 1)] : List FactorBlock).map factorBlockValue).prod) = 3970959864830274425357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_76364612785197585103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3970959864830274425357) ^ 1985479932415137212678 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3970959864830274425357) ^ 305458451140790340412 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3970959864830274425357) ^ 52 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6590051939181799799021 : Nat.Prime 6590051939181799799021 := by
  apply lucas_primality 6590051939181799799021 (2 : ZMod 6590051939181799799021)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 2), (912749576063961191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 2), (912749576063961191, 1)] : List FactorBlock).map factorBlockValue).prod) = 6590051939181799799021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_912749576063961191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6590051939181799799021) ^ 3295025969590899899510 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6590051939181799799021) ^ 1318010387836359959804 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6590051939181799799021) ^ 346844838904305252580 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6590051939181799799021) ^ 7220 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_7901185686054432326081 : Nat.Prime 7901185686054432326081 := by
  apply lucas_primality 7901185686054432326081 (3 : ZMod 7901185686054432326081)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (433, 1), (127108873, 1), (448619891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (433, 1), (127108873, 1), (448619891, 1)] : List FactorBlock).map factorBlockValue).prod) = 7901185686054432326081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_433
      · exact prime_oneHundredFortySevenEO_127108873
      · exact prime_oneHundredFortySevenEO_448619891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7901185686054432326081) ^ 3950592843027216163040 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7901185686054432326081) ^ 1580237137210886465216 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7901185686054432326081) ^ 18247542000125709760 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7901185686054432326081) ^ 62160772096960 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7901185686054432326081) ^ 17612205442880 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_14636105711420750177983 : Nat.Prime 14636105711420750177983 := by
  apply lucas_primality 14636105711420750177983 (3 : ZMod 14636105711420750177983)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1609, 1), (1516066471040061133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1609, 1), (1516066471040061133, 1)] : List FactorBlock).map factorBlockValue).prod) = 14636105711420750177983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_1609
      · exact prime_oneHundredFortySevenEO_1516066471040061133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14636105711420750177983) ^ 7318052855710375088991 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 14636105711420750177983) ^ 4878701903806916725994 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 14636105711420750177983) ^ 9096398826240366798 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 14636105711420750177983) ^ 9654 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_16815058593580838140841 : Nat.Prime 16815058593580838140841 := by
  apply lucas_primality 16815058593580838140841 (6 : ZMod 16815058593580838140841)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (113, 1), (161745465501931879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (113, 1), (161745465501931879, 1)] : List FactorBlock).map factorBlockValue).prod) = 16815058593580838140841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_23
      · exact prime_oneHundredFortySevenEO_113
      · exact prime_oneHundredFortySevenEO_161745465501931879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16815058593580838140841) ^ 8407529296790419070420 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16815058593580838140841) ^ 3363011718716167628168 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16815058593580838140841) ^ 731089504068732093080 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16815058593580838140841) ^ 148805828261777328680 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 16815058593580838140841) ^ 103960 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_42607920028124013205579 : Nat.Prime 42607920028124013205579 := by
  apply lucas_primality 42607920028124013205579 (3 : ZMod 42607920028124013205579)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (3368543, 1), (9539040975421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (3368543, 1), (9539040975421, 1)] : List FactorBlock).map factorBlockValue).prod) = 42607920028124013205579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_3368543
      · exact prime_oneHundredFortySevenEO_9539040975421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42607920028124013205579) ^ 21303960014062006602789 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42607920028124013205579) ^ 14202640009374671068526 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42607920028124013205579) ^ 3277532309855693323506 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42607920028124013205579) ^ 2506348236948471365034 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42607920028124013205579) ^ 12648768333408246 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42607920028124013205579) ^ 4466688018 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_134206584226880430129679 : Nat.Prime 134206584226880430129679 := by
  apply lucas_primality 134206584226880430129679 (6 : ZMod 134206584226880430129679)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (61, 1), (547, 1), (6771271330445161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (61, 1), (547, 1), (6771271330445161, 1)] : List FactorBlock).map factorBlockValue).prod) = 134206584226880430129679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_547
      · exact prime_oneHundredFortySevenEO_6771271330445161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 134206584226880430129679) ^ 67103292113440215064839 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 134206584226880430129679) ^ 44735528075626810043226 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 134206584226880430129679) ^ 12200598566080039102698 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 134206584226880430129679) ^ 2200107938145580821798 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 134206584226880430129679) ^ 245350245387349963674 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 134206584226880430129679) ^ 19819998 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_149481552297456561656377 : Nat.Prime 149481552297456561656377 := by
  apply lucas_primality 149481552297456561656377 (10 : ZMod 149481552297456561656377)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (149, 1), (223, 1), (8926185979551947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (149, 1), (223, 1), (8926185979551947, 1)] : List FactorBlock).map factorBlockValue).prod) = 149481552297456561656377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_149
      · exact prime_oneHundredFortySevenEO_223
      · exact prime_oneHundredFortySevenEO_8926185979551947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 149481552297456561656377) ^ 74740776148728280828188 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 149481552297456561656377) ^ 49827184099152187218792 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 149481552297456561656377) ^ 21354507471065223093768 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 149481552297456561656377) ^ 1003231894613802427224 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 149481552297456561656377) ^ 670320862320433011912 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (10 : ZMod 149481552297456561656377) ^ 16746408 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_268399489068418121600159 : Nat.Prime 268399489068418121600159 := by
  apply lucas_primality 268399489068418121600159 (7 : ZMod 268399489068418121600159)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 2), (1654193, 1), (5246525095081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 2), (1654193, 1), (5246525095081, 1)] : List FactorBlock).map factorBlockValue).prod) = 268399489068418121600159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_47
      · exact prime_oneHundredFortySevenEO_1654193
      · exact prime_oneHundredFortySevenEO_5246525095081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 268399489068418121600159) ^ 134199744534209060800079 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 268399489068418121600159) ^ 38342784152631160228594 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 268399489068418121600159) ^ 5710627426987619608514 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 268399489068418121600159) ^ 162254035090475006 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 268399489068418121600159) ^ 51157572718 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_611093759649767391513167 : Nat.Prime 611093759649767391513167 := by
  apply lucas_primality 611093759649767391513167 (7 : ZMod 611093759649767391513167)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (59, 1), (491, 1), (1993, 1), (4447, 1), (24286998233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (59, 1), (491, 1), (1993, 1), (4447, 1), (24286998233, 1)] : List FactorBlock).map factorBlockValue).prod) = 611093759649767391513167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_59
      · exact prime_oneHundredFortySevenEO_491
      · exact prime_oneHundredFortySevenEO_1993
      · exact prime_oneHundredFortySevenEO_4447
      · exact prime_oneHundredFortySevenEO_24286998233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 611093759649767391513167) ^ 305546879824883695756583 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 611093759649767391513167) ^ 87299108521395341644738 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 611093759649767391513167) ^ 10357521349996057483274 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 611093759649767391513167) ^ 1244590141852886744426 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 611093759649767391513167) ^ 306620049999883287262 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 611093759649767391513167) ^ 137417081099565412978 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (7 : ZMod 611093759649767391513167) ^ 25161353979902 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_999633215591635061252467 : Nat.Prime 999633215591635061252467 := by
  apply lucas_primality 999633215591635061252467 (2 : ZMod 999633215591635061252467)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (61, 1), (50969, 1), (2551726861020299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (61, 1), (50969, 1), (2551726861020299, 1)] : List FactorBlock).map factorBlockValue).prod) = 999633215591635061252467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_61
      · exact prime_oneHundredFortySevenEO_50969
      · exact prime_oneHundredFortySevenEO_2551726861020299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 999633215591635061252467) ^ 499816607795817530626233 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 999633215591635061252467) ^ 333211071863878353750822 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 999633215591635061252467) ^ 142804745084519294464638 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 999633215591635061252467) ^ 16387429763797296086106 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 999633215591635061252467) ^ 19612572653802018114 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 999633215591635061252467) ^ 391747734 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_1222638920286992928708301 : Nat.Prime 1222638920286992928708301 := by
  apply lucas_primality 1222638920286992928708301 (2 : ZMod 1222638920286992928708301)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (13, 2), (37, 1), (72417916157991893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (13, 2), (37, 1), (72417916157991893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222638920286992928708301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_37
      · exact prime_oneHundredFortySevenEO_72417916157991893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222638920286992928708301) ^ 611319460143496464354150 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222638920286992928708301) ^ 407546306762330976236100 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222638920286992928708301) ^ 244527784057398585741660 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222638920286992928708301) ^ 94049147714384071439100 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222638920286992928708301) ^ 33044295142891700775900 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222638920286992928708301) ^ 16883100 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_97
      · exact prime_oneHundredFortySevenEO_719
      · exact prime_oneHundredFortySevenEO_17207
      · exact prime_oneHundredFortySevenEO_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5604425409968232726351827 : Nat.Prime 5604425409968232726351827 := by
  apply lucas_primality 5604425409968232726351827 (2 : ZMod 5604425409968232726351827)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4871, 1), (575284891189512700303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4871, 1), (575284891189512700303, 1)] : List FactorBlock).map factorBlockValue).prod) = 5604425409968232726351827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_4871
      · exact prime_oneHundredFortySevenEO_575284891189512700303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5604425409968232726351827) ^ 2802212704984116363175913 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5604425409968232726351827) ^ 1150569782379025400606 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5604425409968232726351827) ^ 9742 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_7384458549526870484137249 : Nat.Prime 7384458549526870484137249 := by
  apply lucas_primality 7384458549526870484137249 (13 : ZMod 7384458549526870484137249)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 2), (37, 1), (293, 1), (439, 1), (109950250866671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 2), (37, 1), (293, 1), (439, 1), (109950250866671, 1)] : List FactorBlock).map factorBlockValue).prod) = 7384458549526870484137249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_37
      · exact prime_oneHundredFortySevenEO_293
      · exact prime_oneHundredFortySevenEO_439
      · exact prime_oneHundredFortySevenEO_109950250866671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7384458549526870484137249) ^ 3692229274763435242068624 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 7384458549526870484137249) ^ 2461486183175623494712416 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 7384458549526870484137249) ^ 1054922649932410069162464 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 7384458549526870484137249) ^ 199579960798023526598304 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 7384458549526870484137249) ^ 25202930203163380491936 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 7384458549526870484137249) ^ 16821090090038429348832 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (13 : ZMod 7384458549526870484137249) ^ 67161816288 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_8499277775973928836275927 : Nat.Prime 8499277775973928836275927 := by
  apply lucas_primality 8499277775973928836275927 (5 : ZMod 8499277775973928836275927)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8307395039, 1), (511548911305717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8307395039, 1), (511548911305717, 1)] : List FactorBlock).map factorBlockValue).prod) = 8499277775973928836275927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_8307395039
      · exact prime_oneHundredFortySevenEO_511548911305717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8499277775973928836275927) ^ 4249638887986964418137963 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8499277775973928836275927) ^ 1023097822611434 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8499277775973928836275927) ^ 16614790078 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_120605990258927756311013293 : Nat.Prime 120605990258927756311013293 := by
  apply lucas_primality 120605990258927756311013293 (5 : ZMod 120605990258927756311013293)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1831, 1), (4324433, 1), (181331007977881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1831, 1), (4324433, 1), (181331007977881, 1)] : List FactorBlock).map factorBlockValue).prod) = 120605990258927756311013293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_1831
      · exact prime_oneHundredFortySevenEO_4324433
      · exact prime_oneHundredFortySevenEO_181331007977881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 120605990258927756311013293) ^ 60302995129463878155506646 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120605990258927756311013293) ^ 40201996752975918770337764 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120605990258927756311013293) ^ 17229427179846822330144756 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120605990258927756311013293) ^ 65868918765116196783732 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120605990258927756311013293) ^ 27889434351030009324 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120605990258927756311013293) ^ 665115093132 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_129599725550421250443079907 : Nat.Prime 129599725550421250443079907 := by
  apply lucas_primality 129599725550421250443079907 (2 : ZMod 129599725550421250443079907)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1222638920286992928708301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1222638920286992928708301, 1)] : List FactorBlock).map factorBlockValue).prod) = 129599725550421250443079907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_53
      · exact prime_oneHundredFortySevenEO_1222638920286992928708301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 129599725550421250443079907) ^ 64799862775210625221539953 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 129599725550421250443079907) ^ 2445277840573985857416602 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 129599725550421250443079907) ^ 106 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_447920700935863136196314833 : Nat.Prime 447920700935863136196314833 := by
  apply lucas_primality 447920700935863136196314833 (5 : ZMod 447920700935863136196314833)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (30677, 1), (20216341, 1), (366995381807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (30677, 1), (20216341, 1), (366995381807, 1)] : List FactorBlock).map factorBlockValue).prod) = 447920700935863136196314833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_41
      · exact prime_oneHundredFortySevenEO_30677
      · exact prime_oneHundredFortySevenEO_20216341
      · exact prime_oneHundredFortySevenEO_366995381807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 447920700935863136196314833) ^ 223960350467931568098157416 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 447920700935863136196314833) ^ 149306900311954378732104944 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 447920700935863136196314833) ^ 10924895144777149663324752 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 447920700935863136196314833) ^ 14601189846981880112016 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 447920700935863136196314833) ^ 22156368500900491152 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 447920700935863136196314833) ^ 1220507731542576 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_678879812355917565797539669 : Nat.Prime 678879812355917565797539669 := by
  apply lucas_primality 678879812355917565797539669 (2 : ZMod 678879812355917565797539669)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (13, 1), (19, 1), (29, 1), (292518227394514319039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (13, 1), (19, 1), (29, 1), (292518227394514319039, 1)] : List FactorBlock).map factorBlockValue).prod) = 678879812355917565797539669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_19
      · exact prime_oneHundredFortySevenEO_29
      · exact prime_oneHundredFortySevenEO_292518227394514319039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 678879812355917565797539669) ^ 339439906177958782898769834 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 678879812355917565797539669) ^ 226293270785305855265846556 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 678879812355917565797539669) ^ 52221524027378274292118436 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 678879812355917565797539669) ^ 35730516439785135041975772 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 678879812355917565797539669) ^ 23409648701928191924053092 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 678879812355917565797539669) ^ 2320812 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_762251017382082880895483137 : Nat.Prime 762251017382082880895483137 := by
  apply lucas_primality 762251017382082880895483137 (5 : ZMod 762251017382082880895483137)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (13, 1), (29, 1), (292518227394514319039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (13, 1), (29, 1), (292518227394514319039, 1)] : List FactorBlock).map factorBlockValue).prod) = 762251017382082880895483137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_13
      · exact prime_oneHundredFortySevenEO_29
      · exact prime_oneHundredFortySevenEO_292518227394514319039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 762251017382082880895483137) ^ 381125508691041440447741568 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 762251017382082880895483137) ^ 254083672460694293631827712 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 762251017382082880895483137) ^ 58634693644775606222729472 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 762251017382082880895483137) ^ 26284517840761478651568384 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (5 : ZMod 762251017382082880895483137) ^ 2605824 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_3620692332564893684253544901 : Nat.Prime 3620692332564893684253544901 := by
  apply lucas_primality 3620692332564893684253544901 (2 : ZMod 3620692332564893684253544901)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 3620692332564893684253544901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_7
      · exact prime_oneHundredFortySevenEO_171401
      · exact prime_oneHundredFortySevenEO_714027719
      · exact prime_oneHundredFortySevenEO_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3620692332564893684253544901) ^ 1810346166282446842126772450 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620692332564893684253544901) ^ 724138466512978736850708980 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620692332564893684253544901) ^ 517241761794984812036220700 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620692332564893684253544901) ^ 21124102733151461684900 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620692332564893684253544901) ^ 5070800805374467100 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3620692332564893684253544901) ^ 599686818815163100 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_4238859316173534069370003787 : Nat.Prime 4238859316173534069370003787 := by
  apply lucas_primality 4238859316173534069370003787 (2 : ZMod 4238859316173534069370003787)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2473, 1), (9883, 1), (95989, 1), (13907743, 1), (64957301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2473, 1), (9883, 1), (95989, 1), (13907743, 1), (64957301, 1)] : List FactorBlock).map factorBlockValue).prod) = 4238859316173534069370003787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_2473
      · exact prime_oneHundredFortySevenEO_9883
      · exact prime_oneHundredFortySevenEO_95989
      · exact prime_oneHundredFortySevenEO_13907743
      · exact prime_oneHundredFortySevenEO_64957301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4238859316173534069370003787) ^ 2119429658086767034685001893 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4238859316173534069370003787) ^ 1714055526151853647137082 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4238859316173534069370003787) ^ 428904109700853391618942 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4238859316173534069370003787) ^ 44159844525659545045474 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4238859316173534069370003787) ^ 304784127530508298102 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4238859316173534069370003787) ^ 65256087474655605986 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_5111565645973967554240298683 : Nat.Prime 5111565645973967554240298683 := by
  apply lucas_primality 5111565645973967554240298683 (3 : ZMod 5111565645973967554240298683)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (600751, 1), (315113483, 1), (1500099095153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (600751, 1), (315113483, 1), (1500099095153, 1)] : List FactorBlock).map factorBlockValue).prod) = 5111565645973967554240298683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_600751
      · exact prime_oneHundredFortySevenEO_315113483
      · exact prime_oneHundredFortySevenEO_1500099095153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5111565645973967554240298683) ^ 2555782822986983777120149341 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5111565645973967554240298683) ^ 1703855215324655851413432894 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5111565645973967554240298683) ^ 8508626112938584462182 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5111565645973967554240298683) ^ 16221348567220678254 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5111565645973967554240298683) ^ 3407485320463194 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_6684355075504419109391159819 : Nat.Prime 6684355075504419109391159819 := by
  apply lucas_primality 6684355075504419109391159819 (6 : ZMod 6684355075504419109391159819)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3203, 1), (265037, 1), (384941, 1), (929777891069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3203, 1), (265037, 1), (384941, 1), (929777891069, 1)] : List FactorBlock).map factorBlockValue).prod) = 6684355075504419109391159819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_11
      · exact prime_oneHundredFortySevenEO_3203
      · exact prime_oneHundredFortySevenEO_265037
      · exact prime_oneHundredFortySevenEO_384941
      · exact prime_oneHundredFortySevenEO_929777891069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6684355075504419109391159819) ^ 3342177537752209554695579909 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 6684355075504419109391159819) ^ 607668643227674464490105438 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 6684355075504419109391159819) ^ 2086904488137502063500206 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 6684355075504419109391159819) ^ 25220460069742787268914 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 6684355075504419109391159819) ^ 17364622307066327331698 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (6 : ZMod 6684355075504419109391159819) ^ 7189195548432722 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_7899692361959768038371370693 : Nat.Prime 7899692361959768038371370693 := by
  apply lucas_primality 7899692361959768038371370693 (2 : ZMod 7899692361959768038371370693)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (55766203, 1), (1311642100642491833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (55766203, 1), (1311642100642491833, 1)] : List FactorBlock).map factorBlockValue).prod) = 7899692361959768038371370693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_55766203
      · exact prime_oneHundredFortySevenEO_1311642100642491833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7899692361959768038371370693) ^ 3949846180979884019185685346 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7899692361959768038371370693) ^ 2633230787319922679457123564 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7899692361959768038371370693) ^ 141657346869389117964 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7899692361959768038371370693) ^ 6022749924 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_9655179553506383158009453067 : Nat.Prime 9655179553506383158009453067 := by
  apply lucas_primality 9655179553506383158009453067 (2 : ZMod 9655179553506383158009453067)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (600751, 1), (315113483, 1), (1500099095153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (600751, 1), (315113483, 1), (1500099095153, 1)] : List FactorBlock).map factorBlockValue).prod) = 9655179553506383158009453067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_17
      · exact prime_oneHundredFortySevenEO_600751
      · exact prime_oneHundredFortySevenEO_315113483
      · exact prime_oneHundredFortySevenEO_1500099095153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9655179553506383158009453067) ^ 4827589776753191579004726533 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9655179553506383158009453067) ^ 567951738441551950471144298 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9655179553506383158009453067) ^ 16071849324439548428566 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9655179553506383158009453067) ^ 30640325071416836702 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9655179553506383158009453067) ^ 6436361160874922 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_24827604566159270977738593611 : Nat.Prime 24827604566159270977738593611 := by
  apply lucas_primality 24827604566159270977738593611 (2 : ZMod 24827604566159270977738593611)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159270977738593611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_443
      · exact prime_oneHundredFortySevenEO_5604425409968232726351827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24827604566159270977738593611) ^ 12413802283079635488869296805 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 4965520913231854195547718722 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 56044254099682327263518270 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 4430 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySevenEO_86896615981557448422085077631 : Nat.Prime 86896615981557448422085077631 := by
  apply lucas_primality 86896615981557448422085077631 (3 : ZMod 86896615981557448422085077631)
  · rw [← oneHundredFortySevenEOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (281, 1), (359, 1), (2633, 1), (13633, 1), (1747367, 1), (152592491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (281, 1), (359, 1), (2633, 1), (13633, 1), (1747367, 1), (152592491, 1)] : List FactorBlock).map factorBlockValue).prod) = 86896615981557448422085077631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySevenEO_2
      · exact prime_oneHundredFortySevenEO_3
      · exact prime_oneHundredFortySevenEO_5
      · exact prime_oneHundredFortySevenEO_281
      · exact prime_oneHundredFortySevenEO_359
      · exact prime_oneHundredFortySevenEO_2633
      · exact prime_oneHundredFortySevenEO_13633
      · exact prime_oneHundredFortySevenEO_1747367
      · exact prime_oneHundredFortySevenEO_152592491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 86896615981557448422085077631) ^ 43448307990778724211042538815 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 86896615981557448422085077631) ^ 28965538660519149474028359210 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 86896615981557448422085077631) ^ 17379323196311489684417015526 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 86896615981557448422085077631) ^ 309240626268887716804573230 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 86896615981557448422085077631) ^ 242051855101831332652047570 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 86896615981557448422085077631) ^ 33002892511035871030036110 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 86896615981557448422085077631) ^ 6373990756367450188666110 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 86896615981557448422085077631) ^ 49730031516880797463890 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide
    · change (3 : ZMod 86896615981557448422085077631) ^ 569468493581099271930 ≠ 1
      rw [← oneHundredFortySevenEOFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155200 : Nat.totient 173793231963114896844170155200 = 39723935482057574318893056000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (7, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_171401, prime_oneHundredFortySevenEO_714027719, prime_oneHundredFortySevenEO_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155201 : Nat.totient 173793231963114896844170155201 = 173789921371185961451986836096 := by
  rw [← show ((([(52783, 1), (15164213, 1), (26689963, 1), (8135250713, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_52783, prime_oneHundredFortySevenEO_15164213, prime_oneHundredFortySevenEO_26689963, prime_oneHundredFortySevenEO_8135250713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155202 : Nat.totient 173793231963114896844170155202 = 78796312515028758346944537600 := by
  rw [← show ((([(2, 1), (11, 1), (487, 1), (2053, 1), (7901185686054432326081, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_487, prime_oneHundredFortySevenEO_2053, prime_oneHundredFortySevenEO_7901185686054432326081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155203 : Nat.totient 173793231963114896844170155203 = 106943239620333063715339754784 := by
  rw [← show ((([(3, 1), (13, 1), (16603, 1), (268399489068418121600159, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_13, prime_oneHundredFortySevenEO_16603, prime_oneHundredFortySevenEO_268399489068418121600159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155204 : Nat.totient 173793231963114896844170155204 = 86000774579685722149692447744 := by
  rw [← show ((([(2, 2), (97, 1), (447920700935863136196314833, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_97, prime_oneHundredFortySevenEO_447920700935863136196314833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155205 : Nat.totient 173793231963114896844170155205 = 127946470894053036774766064640 := by
  rw [← show ((([(5, 1), (17, 1), (47, 1), (1021, 1), (42607920028124013205579, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_17, prime_oneHundredFortySevenEO_47, prime_oneHundredFortySevenEO_1021, prime_oneHundredFortySevenEO_42607920028124013205579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155206 : Nat.totient 173793231963114896844170155206 = 57931077321038298948056718396 := by
  rw [← show ((([(2, 1), (3, 2), (9655179553506383158009453067, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_9655179553506383158009453067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155207 : Nat.totient 173793231963114896844170155207 = 148821410076584719959813968640 := by
  rw [← show ((([(7, 1), (1321, 1), (4733, 1), (3970959864830274425357, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_1321, prime_oneHundredFortySevenEO_4733, prime_oneHundredFortySevenEO_3970959864830274425357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155208 : Nat.totient 173793231963114896844170155208 = 86474554096434730315299362880 := by
  rw [← show ((([(2, 3), (239, 1), (1483, 1), (677011, 1), (90533246765019143, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_239, prime_oneHundredFortySevenEO_1483, prime_oneHundredFortySevenEO_677011, prime_oneHundredFortySevenEO_90533246765019143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155209 : Nat.totient 173793231963114896844170155209 = 115861911243349588631606603520 := by
  rw [← show ((([(3, 1), (476089, 1), (3188388937, 1), (38163848589571, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_476089, prime_oneHundredFortySevenEO_3188388937, prime_oneHundredFortySevenEO_38163848589571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155210 : Nat.totient 173793231963114896844170155210 = 69060350670857497487104208640 := by
  rw [← show ((([(2, 1), (5, 1), (199, 1), (1093, 1), (1559, 1), (2673164471, 1), (19172900827, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_199, prime_oneHundredFortySevenEO_1093, prime_oneHundredFortySevenEO_1559, prime_oneHundredFortySevenEO_2673164471, prime_oneHundredFortySevenEO_19172900827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155211 : Nat.totient 173793231963114896844170155211 = 167799891073780659448134640960 := by
  rw [← show ((([(29, 1), (356399, 1), (16815058593580838140841, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_29, prime_oneHundredFortySevenEO_356399, prime_oneHundredFortySevenEO_16815058593580838140841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155212 : Nat.totient 173793231963114896844170155212 = 55440242318050583221388160000 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (61, 1), (50051, 1), (5200598791, 1), (24652101373, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_37, prime_oneHundredFortySevenEO_61, prime_oneHundredFortySevenEO_50051, prime_oneHundredFortySevenEO_5200598791, prime_oneHundredFortySevenEO_24652101373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155213 : Nat.totient 173793231963114896844170155213 = 156787787336606083204317279600 := by
  rw [← show ((([(11, 1), (131, 1), (120605990258927756311013293, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_131, prime_oneHundredFortySevenEO_120605990258927756311013293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155214 : Nat.totient 173793231963114896844170155214 = 73836597368753853533747527680 := by
  rw [← show ((([(2, 1), (7, 1), (163, 1), (617, 1), (1231, 1), (14737, 1), (22699, 1), (76163, 1), (3935629, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_163, prime_oneHundredFortySevenEO_617, prime_oneHundredFortySevenEO_1231, prime_oneHundredFortySevenEO_14737, prime_oneHundredFortySevenEO_22699, prime_oneHundredFortySevenEO_76163, prime_oneHundredFortySevenEO_3935629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155215 : Nat.totient 173793231963114896844170155215 = 92512496708472633425271442944 := by
  rw [← show ((([(3, 2), (5, 1), (523, 1), (7384458549526870484137249, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_523, prime_oneHundredFortySevenEO_7384458549526870484137249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155216 : Nat.totient 173793231963114896844170155216 = 80212237502340873013446182400 := by
  rw [← show ((([(2, 4), (13, 1), (3549947, 1), (99231071, 1), (2371919671021, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_13, prime_oneHundredFortySevenEO_3549947, prime_oneHundredFortySevenEO_99231071, prime_oneHundredFortySevenEO_2371919671021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155217 : Nat.totient 173793231963114896844170155217 = 164646219754072701949332291840 := by
  rw [← show ((([(19, 1), (360123441473, 1), (25399657881673291, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_19, prime_oneHundredFortySevenEO_360123441473, prime_oneHundredFortySevenEO_25399657881673291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155218 : Nat.totient 173793231963114896844170155218 = 56304138478396974577265468160 := by
  rw [← show ((([(2, 1), (3, 1), (53, 1), (127, 1), (653, 1), (6590051939181799799021, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_53, prime_oneHundredFortySevenEO_127, prime_oneHundredFortySevenEO_653, prime_oneHundredFortySevenEO_6590051939181799799021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155219 : Nat.totient 173793231963114896844170155219 = 166215012555714711444815036616 := by
  rw [← show ((([(23, 1), (7559, 1), (999633215591635061252467, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_23, prime_oneHundredFortySevenEO_7559, prime_oneHundredFortySevenEO_999633215591635061252467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155220 : Nat.totient 173793231963114896844170155220 = 66829266184468719923476992000 := by
  rw [← show ((([(2, 2), (5, 1), (31, 2), (151, 1), (13888577, 1), (4311662693425463, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_31, prime_oneHundredFortySevenEO_151, prime_oneHundredFortySevenEO_13888577, prime_oneHundredFortySevenEO_4311662693425463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155221 : Nat.totient 173793231963114896844170155221 = 99310418263998186754223695104 := by
  rw [← show ((([(3, 1), (7, 1), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_155440836073, prime_oneHundredFortySevenEO_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155222 : Nat.totient 173793231963114896844170155222 = 81785050335583480867844778912 := by
  rw [← show ((([(2, 1), (17, 1), (5111565645973967554240298683, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_17, prime_oneHundredFortySevenEO_5111565645973967554240298683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155223 : Nat.totient 173793231963114896844170155223 = 170036890068384472731729378624 := by
  rw [← show ((([(59, 1), (313, 1), (643, 1), (14636105711420750177983, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_59, prime_oneHundredFortySevenEO_313, prime_oneHundredFortySevenEO_643, prime_oneHundredFortySevenEO_14636105711420750177983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155224 : Nat.totient 173793231963114896844170155224 = 52664614802016141086396686080 := by
  rw [← show ((([(2, 3), (3, 3), (11, 1), (55766203, 1), (1311642100642491833, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_55766203, prime_oneHundredFortySevenEO_1311642100642491833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155225 : Nat.totient 173793231963114896844170155225 = 137076059740229370507657288000 := by
  rw [← show ((([(5, 2), (71, 1), (469069, 1), (208736198681259388691, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_71, prime_oneHundredFortySevenEO_469069, prime_oneHundredFortySevenEO_208736198681259388691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155226 : Nat.totient 173793231963114896844170155226 = 84733440452036881230601728000 := by
  rw [← show ((([(2, 1), (41, 1), (2473, 1), (9883, 1), (95989, 1), (13907743, 1), (64957301, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_41, prime_oneHundredFortySevenEO_2473, prime_oneHundredFortySevenEO_9883, prime_oneHundredFortySevenEO_95989, prime_oneHundredFortySevenEO_13907743, prime_oneHundredFortySevenEO_64957301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155227 : Nat.totient 173793231963114896844170155227 = 115381135554729510610354483200 := by
  rw [← show ((([(3, 1), (241, 1), (438281, 1), (548456159849912872529, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_241, prime_oneHundredFortySevenEO_438281, prime_oneHundredFortySevenEO_548456159849912872529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155228 : Nat.totient 173793231963114896844170155228 = 74482097131812622974911677440 := by
  rw [← show ((([(2, 2), (7, 1), (103981, 1), (292202129, 1), (204285462728549, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_103981, prime_oneHundredFortySevenEO_292202129, prime_oneHundredFortySevenEO_204285462728549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155229 : Nat.totient 173793231963114896844170155229 = 160351824383772604146665127936 := by
  rw [← show ((([(13, 1), (2393, 1), (29387, 1), (995713, 1), (4344827, 1), (43942513, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_13, prime_oneHundredFortySevenEO_2393, prime_oneHundredFortySevenEO_29387, prime_oneHundredFortySevenEO_995713, prime_oneHundredFortySevenEO_4344827, prime_oneHundredFortySevenEO_43942513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155230 : Nat.totient 173793231963114896844170155230 = 45919668275356768058516688000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (109, 1), (4041299, 1), (13151161881056247751, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_109, prime_oneHundredFortySevenEO_4041299, prime_oneHundredFortySevenEO_13151161881056247751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155231 : Nat.totient 173793231963114896844170155231 = 173793132828552379104769599360 := by
  rw [← show ((([(1755773, 1), (1153423387, 1), (85817476640081, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_1755773, prime_oneHundredFortySevenEO_1153423387, prime_oneHundredFortySevenEO_85817476640081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155232 : Nat.totient 173793231963114896844170155232 = 86896615980459427452482153472 := by
  rw [← show ((([(2, 5), (79139395873, 1), (68626231460786887, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_79139395873, prime_oneHundredFortySevenEO_68626231460786887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155233 : Nat.totient 173793231963114896844170155233 = 114556678232278424979445862400 := by
  rw [← show ((([(3, 2), (103, 1), (641, 1), (71429, 1), (4094685267827061811, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_103, prime_oneHundredFortySevenEO_641, prime_oneHundredFortySevenEO_71429, prime_oneHundredFortySevenEO_4094685267827061811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155234 : Nat.totient 173793231963114896844170155234 = 86061968663821758409905642240 := by
  rw [← show ((([(2, 1), (107, 1), (3821, 1), (859151537, 1), (247384381561903, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_107, prime_oneHundredFortySevenEO_3821, prime_oneHundredFortySevenEO_859151537, prime_oneHundredFortySevenEO_247384381561903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155235 : Nat.totient 173793231963114896844170155235 = 108290890796106606687183168000 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (2269, 1), (24570248051, 1), (8097073720069, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_2269, prime_oneHundredFortySevenEO_24570248051, prime_oneHundredFortySevenEO_8097073720069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155236 : Nat.totient 173793231963114896844170155236 = 54882073251509967424474785792 := by
  rw [← show ((([(2, 2), (3, 1), (19, 1), (762251017382082880895483137, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_19, prime_oneHundredFortySevenEO_762251017382082880895483137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155237 : Nat.totient 173793231963114896844170155237 = 172968734414660922613251255600 := by
  rw [← show ((([(211, 1), (207661, 1), (3966390446257410754147, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_211, prime_oneHundredFortySevenEO_207661, prime_oneHundredFortySevenEO_3966390446257410754147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155238 : Nat.totient 173793231963114896844170155238 = 86884392015416590442438448000 := by
  rw [← show ((([(2, 1), (7151, 1), (1201841, 1), (10110882662367189709, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_7151, prime_oneHundredFortySevenEO_1201841, prime_oneHundredFortySevenEO_10110882662367189709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155239 : Nat.totient 173793231963114896844170155239 = 108539692270610250540228249600 := by
  rw [← show ((([(3, 1), (17, 1), (229, 1), (4759, 1), (13499, 1), (231638049393583901, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_17, prime_oneHundredFortySevenEO_229, prime_oneHundredFortySevenEO_4759, prime_oneHundredFortySevenEO_13499, prime_oneHundredFortySevenEO_231638049393583901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155240 : Nat.totient 173793231963114896844170155240 = 67120144757924241078334380288 := by
  rw [← show ((([(2, 3), (5, 1), (29, 1), (274916209307, 1), (544972419305527, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_29, prime_oneHundredFortySevenEO_274916209307, prime_oneHundredFortySevenEO_544972419305527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155241 : Nat.totient 173793231963114896844170155241 = 169586881433329546866741048960 := by
  rw [← show ((([(43, 1), (1031, 1), (53530439189, 1), (73232680766393, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_43, prime_oneHundredFortySevenEO_1031, prime_oneHundredFortySevenEO_53530439189, prime_oneHundredFortySevenEO_73232680766393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155242 : Nat.totient 173793231963114896844170155242 = 43842726457966873164702256128 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (13, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_13, prime_oneHundredFortySevenEO_23, prime_oneHundredFortySevenEO_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155243 : Nat.totient 173793231963114896844170155243 = 173297008483834031089261113600 := by
  rw [← show ((([(421, 1), (2617, 1), (10103, 1), (26120771, 1), (597737766523, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_421, prime_oneHundredFortySevenEO_2617, prime_oneHundredFortySevenEO_10103, prime_oneHundredFortySevenEO_26120771, prime_oneHundredFortySevenEO_597737766523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155244 : Nat.totient 173793231963114896844170155244 = 85203545275555532465033502720 := by
  rw [← show ((([(2, 2), (83, 1), (139, 1), (3041, 1), (234317, 1), (783613, 1), (6744629923, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_83, prime_oneHundredFortySevenEO_139, prime_oneHundredFortySevenEO_3041, prime_oneHundredFortySevenEO_234317, prime_oneHundredFortySevenEO_783613, prime_oneHundredFortySevenEO_6744629923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155245 : Nat.totient 173793231963114896844170155245 = 92587978681982418796390232640 := by
  rw [← show ((([(3, 1), (5, 1), (911, 1), (594685418827, 1), (21386313733639, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_911, prime_oneHundredFortySevenEO_594685418827, prime_oneHundredFortySevenEO_21386313733639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155246 : Nat.totient 173793231963114896844170155246 = 78996923619597680383713706920 := by
  rw [← show ((([(2, 1), (11, 1), (7899692361959768038371370693, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_7899692361959768038371370693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155247 : Nat.totient 173793231963114896844170155247 = 173786661605363995935982116000 := by
  rw [← show ((([(26701, 1), (2826181, 1), (2303060573119184687, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_26701, prime_oneHundredFortySevenEO_2826181, prime_oneHundredFortySevenEO_2303060573119184687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155248 : Nat.totient 173793231963114896844170155248 = 57931077321038298948056718400 := by
  rw [← show ((([(2, 4), (3, 1), (3620692332564893684253544901, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_3620692332564893684253544901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155249 : Nat.totient 173793231963114896844170155249 = 144934880434372176051795768576 := by
  rw [← show ((([(7, 2), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_37, prime_oneHundredFortySevenEO_31177, prime_oneHundredFortySevenEO_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155250 : Nat.totient 173793231963114896844170155250 = 69517291967191509587079254400 := by
  rw [← show ((([(2, 1), (5, 3), (84978809, 1), (8180544491420909269, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_84978809, prime_oneHundredFortySevenEO_8180544491420909269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155251 : Nat.totient 173793231963114896844170155251 = 112123141220306064936451492800 := by
  rw [← show ((([(3, 4), (31, 1), (73571, 1), (212008267, 1), (4437380717213, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_31, prime_oneHundredFortySevenEO_73571, prime_oneHundredFortySevenEO_212008267, prime_oneHundredFortySevenEO_4437380717213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155252 : Nat.totient 173793231963114896844170155252 = 85047751811385205991957487360 := by
  rw [← show ((([(2, 2), (47, 1), (241716657139, 1), (3824445099696161, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_47, prime_oneHundredFortySevenEO_241716657139, prime_oneHundredFortySevenEO_3824445099696161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155253 : Nat.totient 173793231963114896844170155253 = 173633934707922826587279323920 := by
  rw [← show ((([(1091, 1), (2579046059, 1), (61765933691376437, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_1091, prime_oneHundredFortySevenEO_2579046059, prime_oneHundredFortySevenEO_61765933691376437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155254 : Nat.totient 173793231963114896844170155254 = 57930996722520888016758972000 := by
  rw [← show ((([(2, 1), (3, 1), (719731, 1), (533360389, 1), (75455454880151, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_719731, prime_oneHundredFortySevenEO_533360389, prime_oneHundredFortySevenEO_75455454880151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155255 : Nat.totient 173793231963114896844170155255 = 121584900739513895784134231040 := by
  rw [← show ((([(5, 1), (13, 1), (19, 1), (53030034293, 1), (2653652154361081, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_13, prime_oneHundredFortySevenEO_19, prime_oneHundredFortySevenEO_53030034293, prime_oneHundredFortySevenEO_2653652154361081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155256 : Nat.totient 173793231963114896844170155256 = 70101469523442265446771867648 := by
  rw [← show ((([(2, 3), (7, 1), (17, 2), (31969337, 1), (335902595973800657, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_17, prime_oneHundredFortySevenEO_31969337, prime_oneHundredFortySevenEO_335902595973800657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155257 : Nat.totient 173793231963114896844170155257 = 105296726185764167591726941440 := by
  rw [← show ((([(3, 1), (11, 1), (7333, 1), (7867, 1), (22147, 1), (4122049274682037, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_7333, prime_oneHundredFortySevenEO_7867, prime_oneHundredFortySevenEO_22147, prime_oneHundredFortySevenEO_4122049274682037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155258 : Nat.totient 173793231963114896844170155258 = 86575964252458808137057074720 := by
  rw [← show ((([(2, 1), (271, 1), (9009417817, 1), (35590725838477547, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_271, prime_oneHundredFortySevenEO_9009417817, prime_oneHundredFortySevenEO_35590725838477547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155259 : Nat.totient 173793231963114896844170155259 = 173792606263306086948455773440 := by
  rw [← show ((([(285007, 1), (10920757, 1), (55837323063747041, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_285007, prime_oneHundredFortySevenEO_10920757, prime_oneHundredFortySevenEO_55837323063747041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155260 : Nat.totient 173793231963114896844170155260 = 46030405271727109500842803200 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (281, 1), (359, 1), (2633, 1), (13633, 1), (1747367, 1), (152592491, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_281, prime_oneHundredFortySevenEO_359, prime_oneHundredFortySevenEO_2633, prime_oneHundredFortySevenEO_13633, prime_oneHundredFortySevenEO_1747367, prime_oneHundredFortySevenEO_152592491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155261 : Nat.totient 173793231963114896844170155261 = 173793231601505793843664855392 := by
  rw [← show ((([(480610777, 1), (361609103000024689093, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_480610777, prime_oneHundredFortySevenEO_361609103000024689093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155262 : Nat.totient 173793231963114896844170155262 = 86896615981557448422085077630 := by
  rw [← show ((([(2, 1), (86896615981557448422085077631, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_86896615981557448422085077631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155263 : Nat.totient 173793231963114896844170155263 = 99310415415697182443764666656 := by
  rw [← show ((([(3, 1), (7, 1), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_34858727, prime_oneHundredFortySevenEO_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155264 : Nat.totient 173793231963114896844170155264 = 86896615981557448422085077504 := by
  rw [← show ((([(2, 8), (678879812355917565797539669, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_678879812355917565797539669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155265 : Nat.totient 173793231963114896844170155265 = 128835068822493204741056593920 := by
  rw [← show ((([(5, 1), (23, 1), (67, 1), (73, 1), (457, 1), (1399, 1), (931241, 1), (518968924567, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_23, prime_oneHundredFortySevenEO_67, prime_oneHundredFortySevenEO_73, prime_oneHundredFortySevenEO_457, prime_oneHundredFortySevenEO_1399, prime_oneHundredFortySevenEO_931241, prime_oneHundredFortySevenEO_518968924567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155266 : Nat.totient 173793231963114896844170155266 = 57931076083260596120271642848 := by
  rw [← show ((([(2, 1), (3, 1), (46802489, 1), (618888851413845735299, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_46802489, prime_oneHundredFortySevenEO_618888851413845735299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155267 : Nat.totient 173793231963114896844170155267 = 169554372646941362774800151440 := by
  rw [← show ((([(41, 1), (4238859316173534069370003787, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_41, prime_oneHundredFortySevenEO_4238859316173534069370003787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155268 : Nat.totient 173793231963114896844170155268 = 72897006537682789052911257600 := by
  rw [← show ((([(2, 2), (11, 1), (13, 1), (3203, 1), (265037, 1), (384941, 1), (929777891069, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_13, prime_oneHundredFortySevenEO_3203, prime_oneHundredFortySevenEO_265037, prime_oneHundredFortySevenEO_384941, prime_oneHundredFortySevenEO_929777891069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155269 : Nat.totient 173793231963114896844170155269 = 111866407708597742059848188928 := by
  rw [← show ((([(3, 2), (29, 1), (223637, 1), (26430404149, 1), (112653552233, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_29, prime_oneHundredFortySevenEO_223637, prime_oneHundredFortySevenEO_26430404149, prime_oneHundredFortySevenEO_112653552233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155270 : Nat.totient 173793231963114896844170155270 = 59451744748943012761140170208 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_443, prime_oneHundredFortySevenEO_5604425409968232726351827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155271 : Nat.totient 173793231963114896844170155271 = 170440102121082452319024000000 := by
  rw [← show ((([(53, 1), (2621, 1), (23251, 1), (104917, 1), (512864299805801, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_53, prime_oneHundredFortySevenEO_2621, prime_oneHundredFortySevenEO_23251, prime_oneHundredFortySevenEO_104917, prime_oneHundredFortySevenEO_512864299805801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155272 : Nat.totient 173793231963114896844170155272 = 57114027636265050889426807104 := by
  rw [← show ((([(2, 3), (3, 1), (79, 1), (683, 1), (134206584226880430129679, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_79, prime_oneHundredFortySevenEO_683, prime_oneHundredFortySevenEO_134206584226880430129679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155273 : Nat.totient 173793231963114896844170155273 = 160887838470543567368329512960 := by
  rw [← show ((([(17, 1), (61, 1), (204917, 1), (817854625343146538137, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_17, prime_oneHundredFortySevenEO_61, prime_oneHundredFortySevenEO_204917, prime_oneHundredFortySevenEO_817854625343146538137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155274 : Nat.totient 173793231963114896844170155274 = 81355447109552182638865377408 := by
  rw [← show ((([(2, 1), (19, 1), (89, 1), (1907, 1), (582142943, 1), (46289120187707, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_19, prime_oneHundredFortySevenEO_89, prime_oneHundredFortySevenEO_1907, prime_oneHundredFortySevenEO_582142943, prime_oneHundredFortySevenEO_46289120187707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155275 : Nat.totient 173793231963114896844170155275 = 92689723434536080800527127840 := by
  rw [← show ((([(3, 1), (5, 2), (332072219, 1), (6978129937577018323, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_332072219, prime_oneHundredFortySevenEO_6978129937577018323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155276 : Nat.totient 173793231963114896844170155276 = 86895088668193486850190440640 := by
  rw [← show ((([(2, 2), (57283, 1), (8401381, 1), (90281015094265453, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_57283, prime_oneHundredFortySevenEO_8401381, prime_oneHundredFortySevenEO_90281015094265453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155277 : Nat.totient 173793231963114896844170155277 = 148965627396955625866431561660 := by
  rw [← show ((([(7, 1), (24827604566159270977738593611, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_24827604566159270977738593611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155278 : Nat.totient 173793231963114896844170155278 = 57759172571336584080850532352 := by
  rw [← show ((([(2, 1), (3, 3), (337, 1), (23641649, 1), (403953554336384389, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_337, prime_oneHundredFortySevenEO_23641649, prime_oneHundredFortySevenEO_403953554336384389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155279 : Nat.totient 173793231963114896844170155279 = 157993847239080470536969258560 := by
  rw [← show ((([(11, 1), (1375336807337, 1), (11487647709008197, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_1375336807337, prime_oneHundredFortySevenEO_11487647709008197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155280 : Nat.totient 173793231963114896844170155280 = 69512509375572440127694593024 := by
  rw [← show ((([(2, 4), (5, 1), (14533, 1), (149481552297456561656377, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_14533, prime_oneHundredFortySevenEO_149481552297456561656377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155281 : Nat.totient 173793231963114896844170155281 = 106949221804196976380859072000 := by
  rw [← show ((([(3, 1), (13, 3), (232801, 1), (113265254864242715791, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_13, prime_oneHundredFortySevenEO_232801, prime_oneHundredFortySevenEO_113265254864242715791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155282 : Nat.totient 173793231963114896844170155282 = 82427371230786748006581411840 := by
  rw [← show ((([(2, 1), (31, 1), (59, 1), (349, 1), (21013, 1), (4102229, 1), (1579267763873, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_31, prime_oneHundredFortySevenEO_59, prime_oneHundredFortySevenEO_349, prime_oneHundredFortySevenEO_21013, prime_oneHundredFortySevenEO_4102229, prime_oneHundredFortySevenEO_1579267763873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155283 : Nat.totient 173793231963114896844170155283 = 173660146048389426044859577600 := by
  rw [← show ((([(1307, 1), (1512569, 1), (87910768541306777201, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_1307, prime_oneHundredFortySevenEO_1512569, prime_oneHundredFortySevenEO_87910768541306777201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155284 : Nat.totient 173793231963114896844170155284 = 48500424017800441163614126080 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_43, prime_oneHundredFortySevenEO_4282273, prime_oneHundredFortySevenEO_32701811, prime_oneHundredFortySevenEO_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155285 : Nat.totient 173793231963114896844170155285 = 137658004650792439427800224000 := by
  rw [← show ((([(5, 1), (101, 1), (287395861, 1), (406236319, 1), (2947692823, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_101, prime_oneHundredFortySevenEO_287395861, prime_oneHundredFortySevenEO_406236319, prime_oneHundredFortySevenEO_2947692823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155286 : Nat.totient 173793231963114896844170155286 = 84534952597440002032142268000 := by
  rw [← show ((([(2, 1), (37, 1), (6451, 1), (69914037331, 1), (5207265435319, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_37, prime_oneHundredFortySevenEO_6451, prime_oneHundredFortySevenEO_69914037331, prime_oneHundredFortySevenEO_5207265435319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155287 : Nat.totient 173793231963114896844170155287 = 115084556288774070393454956528 := by
  rw [← show ((([(3, 2), (149, 1), (129599725550421250443079907, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_149, prime_oneHundredFortySevenEO_129599725550421250443079907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155288 : Nat.totient 173793231963114896844170155288 = 83118500416913066118113139072 := by
  rw [← show ((([(2, 3), (23, 1), (76141909, 1), (113251147, 1), (109533929059, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_23, prime_oneHundredFortySevenEO_76141909, prime_oneHundredFortySevenEO_113251147, prime_oneHundredFortySevenEO_109533929059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155289 : Nat.totient 173793231963114896844170155289 = 173793231931274535307410684624 := by
  rw [← show ((([(5458268173, 1), (31840361531301202493, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_5458268173, prime_oneHundredFortySevenEO_31840361531301202493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155290 : Nat.totient 173793231963114896844170155290 = 39652685008713447624695500800 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (110623, 1), (126173, 1), (2219515269182291, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_17, prime_oneHundredFortySevenEO_110623, prime_oneHundredFortySevenEO_126173, prime_oneHundredFortySevenEO_2219515269182291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155291 : Nat.totient 173793231963114896844170155291 = 148965112121222445724952404128 := by
  rw [← show ((([(7, 1), (289103, 1), (20288258719, 1), (4232894525309, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_289103, prime_oneHundredFortySevenEO_20288258719, prime_oneHundredFortySevenEO_4232894525309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155292 : Nat.totient 173793231963114896844170155292 = 86261808891876070461113779200 := by
  rw [← show ((([(2, 2), (137, 1), (185401, 1), (1438973, 1), (1188741935720723, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_137, prime_oneHundredFortySevenEO_185401, prime_oneHundredFortySevenEO_1438973, prime_oneHundredFortySevenEO_1188741935720723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155293 : Nat.totient 173793231963114896844170155293 = 109717852004252902819885795200 := by
  rw [← show ((([(3, 1), (19, 3), (2371, 1), (2367054121, 1), (1504911844199, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_19, prime_oneHundredFortySevenEO_2371, prime_oneHundredFortySevenEO_2367054121, prime_oneHundredFortySevenEO_1504911844199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155294 : Nat.totient 173793231963114896844170155294 = 80212260906053029312693917816 := by
  rw [← show ((([(2, 1), (13, 1), (6684355075504419109391159819, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_13, prime_oneHundredFortySevenEO_6684355075504419109391159819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155295 : Nat.totient 173793231963114896844170155295 = 139034585561468899516465797280 := by
  rw [← show ((([(5, 1), (15408878399, 1), (2255754474308703341, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_15408878399, prime_oneHundredFortySevenEO_2255754474308703341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155296 : Nat.totient 173793231963114896844170155296 = 57115146654544801779774222720 := by
  rw [← show ((([(2, 5), (3, 2), (71, 1), (8499277775973928836275927, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_71, prime_oneHundredFortySevenEO_8499277775973928836275927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155297 : Nat.totient 173793231963114896844170155297 = 173378448555195555889245092064 := by
  rw [← show ((([(419, 1), (71504707, 1), (5800750756247764409, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_419, prime_oneHundredFortySevenEO_71504707, prime_oneHundredFortySevenEO_5800750756247764409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155298 : Nat.totient 173793231963114896844170155298 = 71119281435621719828045070336 := by
  rw [← show ((([(2, 1), (7, 2), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_7, prime_oneHundredFortySevenEO_29, prime_oneHundredFortySevenEO_113, prime_oneHundredFortySevenEO_449, prime_oneHundredFortySevenEO_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155299 : Nat.totient 173793231963114896844170155299 = 113340781789761657638729924352 := by
  rw [← show ((([(3, 1), (47, 1), (2017, 1), (611093759649767391513167, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_3, prime_oneHundredFortySevenEO_47, prime_oneHundredFortySevenEO_2017, prime_oneHundredFortySevenEO_611093759649767391513167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155300 : Nat.totient 173793231963114896844170155300 = 69517285428282633416364599200 := by
  rw [← show ((([(2, 2), (5, 2), (9449183, 1), (183924083133023137391, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_2, prime_oneHundredFortySevenEO_5, prime_oneHundredFortySevenEO_9449183, prime_oneHundredFortySevenEO_183924083133023137391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySevenEO_173793231963114896844170155301 : Nat.totient 173793231963114896844170155301 = 156365044539656178851684801280 := by
  rw [← show ((([(11, 2), (97, 1), (1037719019, 1), (14269080191837767, 1)] : List FactorBlock).map factorBlockValue).prod) = 173793231963114896844170155301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySevenEO_11, prime_oneHundredFortySevenEO_97, prime_oneHundredFortySevenEO_1037719019, prime_oneHundredFortySevenEO_14269080191837767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortySevenEO : certifiedKill 1 173793231963114896844170155199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortySevenEO_173793231963114896844170155200, phi_oneHundredFortySevenEO_173793231963114896844170155201, phi_oneHundredFortySevenEO_173793231963114896844170155202,
    phi_oneHundredFortySevenEO_173793231963114896844170155203, phi_oneHundredFortySevenEO_173793231963114896844170155204, phi_oneHundredFortySevenEO_173793231963114896844170155205,
    phi_oneHundredFortySevenEO_173793231963114896844170155206, phi_oneHundredFortySevenEO_173793231963114896844170155207, phi_oneHundredFortySevenEO_173793231963114896844170155208,
    phi_oneHundredFortySevenEO_173793231963114896844170155209, phi_oneHundredFortySevenEO_173793231963114896844170155210, phi_oneHundredFortySevenEO_173793231963114896844170155211,
    phi_oneHundredFortySevenEO_173793231963114896844170155212, phi_oneHundredFortySevenEO_173793231963114896844170155213, phi_oneHundredFortySevenEO_173793231963114896844170155214,
    phi_oneHundredFortySevenEO_173793231963114896844170155215, phi_oneHundredFortySevenEO_173793231963114896844170155216, phi_oneHundredFortySevenEO_173793231963114896844170155217,
    phi_oneHundredFortySevenEO_173793231963114896844170155218, phi_oneHundredFortySevenEO_173793231963114896844170155219, phi_oneHundredFortySevenEO_173793231963114896844170155220,
    phi_oneHundredFortySevenEO_173793231963114896844170155221, phi_oneHundredFortySevenEO_173793231963114896844170155222, phi_oneHundredFortySevenEO_173793231963114896844170155223,
    phi_oneHundredFortySevenEO_173793231963114896844170155224, phi_oneHundredFortySevenEO_173793231963114896844170155225, phi_oneHundredFortySevenEO_173793231963114896844170155226,
    phi_oneHundredFortySevenEO_173793231963114896844170155227, phi_oneHundredFortySevenEO_173793231963114896844170155228, phi_oneHundredFortySevenEO_173793231963114896844170155229,
    phi_oneHundredFortySevenEO_173793231963114896844170155230, phi_oneHundredFortySevenEO_173793231963114896844170155231, phi_oneHundredFortySevenEO_173793231963114896844170155232,
    phi_oneHundredFortySevenEO_173793231963114896844170155233, phi_oneHundredFortySevenEO_173793231963114896844170155234, phi_oneHundredFortySevenEO_173793231963114896844170155235,
    phi_oneHundredFortySevenEO_173793231963114896844170155236, phi_oneHundredFortySevenEO_173793231963114896844170155237, phi_oneHundredFortySevenEO_173793231963114896844170155238,
    phi_oneHundredFortySevenEO_173793231963114896844170155239, phi_oneHundredFortySevenEO_173793231963114896844170155240, phi_oneHundredFortySevenEO_173793231963114896844170155241,
    phi_oneHundredFortySevenEO_173793231963114896844170155242, phi_oneHundredFortySevenEO_173793231963114896844170155243, phi_oneHundredFortySevenEO_173793231963114896844170155244,
    phi_oneHundredFortySevenEO_173793231963114896844170155245, phi_oneHundredFortySevenEO_173793231963114896844170155246, phi_oneHundredFortySevenEO_173793231963114896844170155247,
    phi_oneHundredFortySevenEO_173793231963114896844170155248, phi_oneHundredFortySevenEO_173793231963114896844170155249, phi_oneHundredFortySevenEO_173793231963114896844170155250,
    phi_oneHundredFortySevenEO_173793231963114896844170155251, phi_oneHundredFortySevenEO_173793231963114896844170155252, phi_oneHundredFortySevenEO_173793231963114896844170155253,
    phi_oneHundredFortySevenEO_173793231963114896844170155254, phi_oneHundredFortySevenEO_173793231963114896844170155255, phi_oneHundredFortySevenEO_173793231963114896844170155256,
    phi_oneHundredFortySevenEO_173793231963114896844170155257, phi_oneHundredFortySevenEO_173793231963114896844170155258, phi_oneHundredFortySevenEO_173793231963114896844170155259,
    phi_oneHundredFortySevenEO_173793231963114896844170155260, phi_oneHundredFortySevenEO_173793231963114896844170155261, phi_oneHundredFortySevenEO_173793231963114896844170155262,
    phi_oneHundredFortySevenEO_173793231963114896844170155263, phi_oneHundredFortySevenEO_173793231963114896844170155264, phi_oneHundredFortySevenEO_173793231963114896844170155265,
    phi_oneHundredFortySevenEO_173793231963114896844170155266, phi_oneHundredFortySevenEO_173793231963114896844170155267, phi_oneHundredFortySevenEO_173793231963114896844170155268,
    phi_oneHundredFortySevenEO_173793231963114896844170155269, phi_oneHundredFortySevenEO_173793231963114896844170155270, phi_oneHundredFortySevenEO_173793231963114896844170155271,
    phi_oneHundredFortySevenEO_173793231963114896844170155272, phi_oneHundredFortySevenEO_173793231963114896844170155273, phi_oneHundredFortySevenEO_173793231963114896844170155274,
    phi_oneHundredFortySevenEO_173793231963114896844170155275, phi_oneHundredFortySevenEO_173793231963114896844170155276, phi_oneHundredFortySevenEO_173793231963114896844170155277,
    phi_oneHundredFortySevenEO_173793231963114896844170155278, phi_oneHundredFortySevenEO_173793231963114896844170155279, phi_oneHundredFortySevenEO_173793231963114896844170155280,
    phi_oneHundredFortySevenEO_173793231963114896844170155281, phi_oneHundredFortySevenEO_173793231963114896844170155282, phi_oneHundredFortySevenEO_173793231963114896844170155283,
    phi_oneHundredFortySevenEO_173793231963114896844170155284, phi_oneHundredFortySevenEO_173793231963114896844170155285, phi_oneHundredFortySevenEO_173793231963114896844170155286,
    phi_oneHundredFortySevenEO_173793231963114896844170155287, phi_oneHundredFortySevenEO_173793231963114896844170155288, phi_oneHundredFortySevenEO_173793231963114896844170155289,
    phi_oneHundredFortySevenEO_173793231963114896844170155290, phi_oneHundredFortySevenEO_173793231963114896844170155291, phi_oneHundredFortySevenEO_173793231963114896844170155292,
    phi_oneHundredFortySevenEO_173793231963114896844170155293, phi_oneHundredFortySevenEO_173793231963114896844170155294, phi_oneHundredFortySevenEO_173793231963114896844170155295,
    phi_oneHundredFortySevenEO_173793231963114896844170155296, phi_oneHundredFortySevenEO_173793231963114896844170155297, phi_oneHundredFortySevenEO_173793231963114896844170155298,
    phi_oneHundredFortySevenEO_173793231963114896844170155299, phi_oneHundredFortySevenEO_173793231963114896844170155300, phi_oneHundredFortySevenEO_173793231963114896844170155301]

end TotientTailPeriodKiller
end Erdos249257
